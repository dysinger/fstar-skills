---
name: fstar-proofs
description: F* proof patterns — lemmas, SMTPat, induction, GADT type-refinement barriers, mutual rec, Ghost/Stack bridging, and common proof errors.
---

# F\* Proof Patterns

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
> Cross-reference: [fstar index](../SKILL.md).

---

## 1. Lemma Structure

```fstar
(* Simple lemma *)
let lemma_add_comm (x y: int) : Lemma (x + y = y + x) = ()

(* With requires/ensures *)
let lemma_head_append (x: 'a) (xs: list 'a) (ys: list 'a) :
  Lemma (ensures (hd (x::xs @ ys) == x)) = ()

(* With SMTPat *)
let lemma_append_length (xs ys: list 'a) :
  Lemma (ensures length (xs @ ys) = length xs + length ys)
  [SMTPat (length (xs @ ys))] = ...

(* Recursive — induction *)
let rec lemma_append_assoc (xs ys zs: list 'a) :
  Lemma (ensures (xs @ ys) @ zs == xs @ (ys @ zs)) =
  match xs with
  | [] -> ()
  | h :: t -> lemma_append_assoc t ys zs
```

---

## 2. SMT Capabilities and Limits

### SMT CAN prove
- Concrete pattern matches, simple algebraic properties (commutativity)
- Non-recursive equivalences, `option`/`either` properties
- Arithmetic on bounded values, single-step unfolding of non-mutual `let rec`
- Equality substitution along `==` chains (after `lemma_eq_elim`)

### SMT CANNOT prove
- Quantified recursive list properties
- Non-linear arithmetic (multiplication/division/modulo on variables)
- Properties requiring induction over recursive types
- Chained roundtrip through compound combinators — needs explicit lemma chaining
- Multi-step mutual-rec unfolding (even in defining module)
- Congruence closure on mutual-rec symbols across module boundaries

---

## 3. SMTPat

### Construction rules
Z3 rejects patterns containing: function-valued arguments, unit values, `List.Tot.length` calls, `op_Subtraction` on `nat`. Working patterns: bare variables, concrete constructors.

### Trigger conflicts
Overlapping SMTPat patterns cause unpredictable SMT firing. Fix: one combined lemma per constructor.

### Performance
Each `[SMTPat]` fires in every SMT query across every importing module. Prefer explicit calls unless the lemma MUST fire automatically.

### Unfold lemma pattern
```fstar
let lemma_product_decode (c1 c2: codec a) (input: seq byte) : Lemma
  (ensures decode (Product c1 c2) input == ...)
  [SMTPat (decode (Product c1 c2) input)]
  = ()
```

---

## 4. Induction

### Induct on input, not fuel
Prefer `decreases` on the data being consumed, not a separate fuel counter. Fuel is opaque to SMT.

### List induction vs nat induction
Prefer induction on the output list rather than a count — avoids `n-1 : int` issues:
```fstar
let rec lemma_by_list (vs: list a) : Lemma (ensures ...) (decreases vs) =
  match vs with
  | [] -> ()
  | v :: tl -> lemma_by_list tl; ...
```

### Lexicographic decreases for mutual rec
```fstar
let rec lemma_dispatcher (c: codec a) ...
  : Lemma ... (decreases %[codec_depth c; 0; 0])
and lemma_aux (c: codec a) (vs: list a) ...
  : Lemma ... (decreases %[codec_depth c; 1; List.Tot.length vs])
```

---

## 5. SMT Context Pollution

A module opening another with many SMTPat lemmas can prevent SMT from proving even trivial recursive properties. **Fix**: isolate lemmas in a clean module that does NOT open the polluted one.

---

## 6. Prop-Valued Predicate Without hasEq

When a proof requires equality on a type without `hasEq`, use `prop` instead of `bool`:

```fstar
(* WRONG — bool needs hasEq *)
let wfcv (v: a) : bool = v == x   (* Error: hasEq a not found *)

(* RIGHT — prop equality is always available *)
let wfcv_prop (v: a) : prop = v == x
```

`prop` uses `==` (propositional equality) — no `hasEq` needed. Must be standalone `let rec` — mutual-rec functions are opaque to SMT.

---

## 7. Ghost/Stack Bridge (Error 53)

Calling a Lemma (Ghost) from Stack with `HST.get()` values triggers Error 53.

**Fix**: pass the heap to the lemma as a parameter:
```fstar
let lemma_bridge (buf: buffer byte) (h: HS.mem) : Lemma
  (requires ...) (ensures ...) = ()

(* At call site — capture h0 at function START *)
let h0_snap = HST.get () in
lemma_bridge buf h0_snap;  (* OK *)
```

`HST.get()` at START gives `h_init == h0` from Hoare pre-condition. At END it's a fresh SMT variable not unified with `h1`. Never compute `Seq.slice` in Stack and pass to Lemma.

### Pure-spec bridge (eliminating recursive Stack)

Recursive Stack decode functions create fresh heap variables per recursive call — SMT cannot equate these to outer `h1`. **Fix**: eliminate ALL recursive Stack calls. Pipeline: `Stack read → lemma bridge → pure spec → convert result`.

### Stack encode→decode roundtrip (post-condition chaining)

SMT cannot chain: `encode` Stack post-condition → pure roundtrip lemma → `decode` Stack post-condition.  The encode post-condition describes a buffer slice; the decode post-condition references individual buffer indices.  SMT cannot connect the slice equality to the index lookups through a pure lemma call.

**Fix**: write structural roundtrip lemmas that inline the encode logic (direct buffer writes) and call the pure roundtrip lemma directly.  Do NOT call the encode/decode Stack functions and attempt post-condition chaining.  The individual functions remain verified via their own post-conditions; the structural lemma proves the roundtrip property without SMT bridge gaps.

### Buffer slice to index bridging

SMT cannot connect `Seq.slice (as_seq h buf) off (off+n) == expected`
to `LB.index buf off == expected_0`.  Slice equality does not automatically
imply element-wise equality over `LB.index` — the SMT sees `as_seq` as an
uninterpreted function in the Stack effect context.

**Fix**: Write a pure `Lemma` (not Stack) parameterized by the heap:

```fstar
let lemma_slice_index_match (w: wire_addr) (s: Seq.seq U8.t) (off: nat) : Lemma
  (requires
    off + 4 <= Seq.length s /\
    Seq.slice s off (off + 4) `Seq.equal` Seq.seq_of_list (encode_spec w))
  (ensures
    Seq.index s off == w.octet0 /\
    Seq.index s (off + 1) == w.octet1 /\
    Seq.index s (off + 2) == w.octet2 /\
    Seq.index s (off + 3) == w.octet3)
  = Seq.lemma_index_slice s off (off + 4) 0;
    Seq.lemma_index_slice s off (off + 4) 1;
    Seq.lemma_index_slice s off (off + 4) 2;
    Seq.lemma_index_slice s off (off + 4) 3;
    ()

let lemma_decode_match (w: wire_addr) (buf: LB.buffer U8.t) (off len: U32.t) (h0: HS.mem)
  : Lemma (requires ... slice == encode_spec ...) (ensures True)
  = lemma_slice_index_match w (LB.as_seq h0 buf) (U32.v off)
```

Key points:
- `Lemma` (Ghost) CAN call `Seq.lemma_index_slice` (also Ghost) — no barrier
- The lemma takes `h0` as explicit parameter, not captured via `HST.get()`
- Callers in Stack context use `lemma_decode_match w buf off len (HST.get ())`
- `Seq.index (as_seq h buf) off` is definitionally equal to `LB.index buf off`
  in heap `h`, so the lemma's post-condition connects to buffer reads
- Pattern works for any fixed-size structure: just extend the lemma for more indices

---

## 8. Error Position Handling

In compound decode functions, error positions from recursive calls are ABSOLUTE positions. Pass through without shifting:
```fstar
(* WRONG — double-counts *)
| Inl err -> Inl ({err with pos = U32.add err.pos n1})
(* CORRECT *)
| Inl err -> Inl err
```

---

## 9. `--admit_smt_queries` Hazards

### Parameter-order bugs silently masked
Adjacent `nat`/`int` parameters can be swapped undetected — `nat <: int` but `int` is NOT `<: nat`. `--admit_smt_queries true` admits the subtyping failure. **Detection**: remove the flag, check for Error 19.

### Admit scope narrowing
Use `--admit_smt_queries true` with `--split_queries always` to admit only stubborn branches. Document which branches fail. Goal: shrink admit scope to zero.

---

## 10. GADT Proof Patterns

### Type refinement not visible to SMT
When pattern-matching a GADT, the type-checker knows type index equalities but SMT does NOT. **Fix**:
```fstar
| UInt8 ->
    assert (a == int);           (* SMT sees this *)
    let v_int : int = v in       (* type-checker coerces *)
    concrete_lemma v_int rest
```

Use `--split_queries always` so each branch is independent.

### GADT `#a` binder must be named
```fstar
(* WRONG — let vs : list a = v uses outer a, producing list (list a) *)
| Count _ c' -> let vs : list a = v in helper c' vs

(* RIGHT — #a_elem binds inner element type *)
| Count #a_elem n c' -> let vs : list a_elem = v in helper #a_elem c' vs
```

### GADT opacity — affects all function types
SMT cannot evaluate `let rec` functions at polymorphic GADT constructors. **What works**: monomorphic type parameters, functions recursing on the list not the codec. **What fails**: polymorphic `Count n ec` case, SMTPat lemmas with `()` body referencing definitional equality.

**Fix**: Mutual-rec list companions:
```fstar
let rec wfcv_prop (c: codec a) (v: a) : Tot prop =
  match c with
  | Count n c' -> ... wfcv_prop_of_list c' (v <: list _)
  ...
and wfcv_prop_of_list (c: codec a) (vs: list a) : Tot prop =
  match vs with
  | hd :: tl -> wfcv_prop c hd /\ wfcv_prop_of_list c tl
  | [] -> True
```

### Bridge lemma pattern
When a chain lemma proves the ensures for an explicit constructor but the dispatcher uses generic `c`:
```fstar
let lemma_bridge_product (c: codec (a & b)) (c1: codec a) (c2: codec b)
  (v: a & b) (eq_c: squash (c == Product c1 c2)) : Lemma ...
  = ()
```
Call with `let eq_c : squash (c == Product c1 c2) = () in lemma_bridge_product ...`.

### Mutual-rec — no cross-module congruence closure
Mutual-rec functions get opaque SMT symbols in importing modules. Congruence closure does not apply. **Workarounds**: (1) avoid cons-pattern matching — use `if` guards and `List.Tot.hd`/`tl`, (2) prove lemmas in the defining module, (3) use standalone (non-mutual) recursion.

### GADT vs value-parameter architecture
LowParse uses function types + records, not a GADT. Combinators take parsers as VALUE parameters — SMT can call them directly. **Lesson**: when SMT must extract properties from a compound structure, represent it as a **value** taking sub-properties as arguments, not as a type-indexed constructor.

---

## 11. Seq Lemma Recipes

```fstar
(* Slice after encoded prefix *)
let lemma_slice_after_prefix (enc rest: seq byte) : Lemma
  (ensures slice (enc ++ rest) (length enc) (length (enc ++ rest)) == rest)
  = lemma_len_append enc rest; lemma_eq_intro ...

(* Slice of cons *)
let lemma_slice_cons (x: 'a) (s: seq 'a) : Lemma
  (ensures slice (cons x s) 1 (length s + 1) == s)

(* Bytes self-prefix *)
let rec lemma_bytes_self_prefix (bs: list byte) (rest: seq byte) : Lemma
  (ensures bytes_decode bs (seq_of_list bs ++ rest) == Inr ((), length bs))

(* Cons-append interchange *)
let lemma_seq_cons_append (x: 'a) (s1 s2: seq 'a) : Lemma
  (ensures cons x s1 ++ s2 == cons x (s1 ++ s2))
  [SMTPat (cons x s1 ++ s2)]
```

Use `==` not `Seq.equal` in ensures — give SMT a substitution path with `lemma_eq_elim` in the body.

### Seq abstraction barrier (cross-module)

`FStar.Seq.fsti` hides the concrete representation (`MkSeq (list a)`).
All `seq` operations (`append`, `cons`, `create`, `seq_of_list`,
`seq_to_list`) are OPAQUE from any module that opens `FStar.Seq`
(which is every module).  This is the same fundamental problem as
`noeq type` field opacity (§18) — definitional equalities that hold
within `FStar.Seq.Base.fst` cannot be proven from outside.

**Consequence (REVISED)**: `seq_to_list (seq_of_list l ++ s) ==
l @ seq_to_list s` was ORIGINALLY recorded as unprovable, but it IS provable
0-admit by induction on [l] using the TRANSPARENT internal stdlib bridges
[FStar.Seq.Base.lemma_seq_of_list_cons], [FStar.Seq.Properties.append_cons],
and [FStar.Seq.Base.lemma_seq_to_list_cons] (each a transparent [= ()] in
[FStar.Seq.Base.fst]).  The proven form is a bridge lemma
`lemma_seq_to_list_of_list_append` (precedent: a 16-element wire-format
structure proved it under `--z3rlimit 2000`).
The earlier "unprovable" claim conflated SMT's failure to chain these
automatically with genuine unprovability — the explicit internal-bridge chain
proves it.  This is the bridge a [Seq.seq_to_list]-at-the-boundary decoder
needs for a GENERAL-[r] roundtrip (§60).

**Fix**: for a [seq_of_list]-prefix, bridge with
`lemma_seq_to_list_of_list_append l s`; for
fully-general [Seq.append s1 s2] (both symbolic), the distribution fact is
STILL unproven.  Prefer Seq-native scans ([Seq.index]/[tail])
for single-byte content; use [seq_to_list]-at-the-boundary + the bridge only
where a multi-byte delimiter forces list-level lookahead (§60).

### Seq↔list index bridging — `lemma_seq_of_list_index`

`Seq.index (Seq.seq_of_list l) k` requires unfolding `k` cons layers
of `l`.  SMT can unfold ~12 layers; for deeper lists (e.g., a 16-element
wire format), `Seq.index (seq_of_list l) k` is uninterpreted for
k >= 13.

**The bridge lemma** ([FStar.Seq.Properties.lemma_seq_of_list_index]):

```fstar
val lemma_seq_of_list_index (#a:Type) (l:list a) (i:nat{i < List.Tot.length l})
  : Lemma (Seq.index (Seq.seq_of_list l) i == List.Tot.index l i)
```

This converts the opaque `Seq.index (seq_of_list ...)` into
`List.Tot.index`, which [assert_norm] CAN compute (normalizer handles
arbitrary-depth list indexing, SMT cannot).

**Full 3-step per-index chain** (for 16-byte slice-to-index bridging):
1. `Seq.lemma_index_slice s off (off+16) k` — slice index → buffer index
2. `Seq.Properties.lemma_seq_of_list_index l k` — seq_index → list_index
3. `assert_norm (List.Tot.index l k == expected_k)` — normalizer computes value
4. `assert (Seq.index s (off+k) == expected_k)` — SMT chains 1-3

Use `--split_queries always` and `--z3rlimit 400` — each of the 16
indices proves in its own SMT query.

**When to apply**: Any lemma bridging `Seq.equal` on a slice of >12
elements to individual `Seq.index` equalities.  For <=4 elements, the
simpler 4-call `Seq.lemma_index_slice` pattern (`lemma_slice_index_match`)
works directly.

---

## 12. Common Errors

| Error | Cause | Fix |
|---|---|---|
| 19 (subtyping) | GADT type index mismatch | `assert (a == T); let v_T : T = v; lemma(v_T)` |
| 19 (#a binder) | Unnamed existential type parameter | `Count #a_elem n c'` — name the binder |
| 19 (int/nat) | `nat - nat` returns `int` | `if a >= b then a - b else 0` |
| 53 (Ghost/Stack) | Computing Ghost in Stack, passing to Lemma | Pass HEAP to lemma instead |
| 56 (bound variable) | `FStar.Int.Cast` refined return in Stack | Wrap in `inline_for_extraction Tot` helper |
| 66 (implicit) | GADT + Type0-valued return function | Explicit `#a1 #a2` on `fst`/`snd` |
| 72 (identifier not found) | Forward reference in `#push-options` block | Move definition before call site; `val` declarations don't always help in `.fst` files with nested push-options |
| 168 (nested push) | `#push-options` inside match branch | Extract to separate lemma function |
| 189 (C.Loops) | Wrong `while` API | See fstar-lowstar § C.Loops |
| 189 (Seq.length on list) | `open FStar.Seq` shadows `List.Tot.length` — `length (r: list byte)` resolves to `Seq.length` which expects `seq` | Use `List.Tot.length` or `L.length` explicitly; never bare `length` on `list` refinements when `FStar.Seq` is opened |
| 242 (local rec) | Local `let rec` not SMT-encoded | Use top-level `let rec` or `List.Tot.fold_right` |
| 297 (or-pattern) | Different type bindings in GADT or-pattern | Split into separate cases |

---

## 13. Common Gotchas

- `else` of `if i < n` gives `~(i < n)`, NOT `i >= n`. Use positive condition: `if i >= n then ... else ...`
- `nat - nat` returns `int`. Guard with `if a >= b`.
- `*` without `open FStar.Mul` is a TUPLE TYPE operator. Open `FStar.Mul` for multiplication.
- `decreases` must be on the SAME LINE as the return type for 3+ parameter functions.
- Pure effect name: a constructor named `Pure` shadows `Prims.Pure`. Use `Tot` or fully-qualified `Prims.Pure`.
- `Seq.equal` in ensures: SMT doesn't substitute. Use `==` with `lemma_eq_elim` in the body.

---

## 14. SMT and List `@` (Append) — The Cons-Only Rule

**Critical lesson**: SMT cannot reason through `@` (list append)
in encode/decode chains. When encode produces output via `[chars] @ rest` and
decode consumes it via `bytes @ tl`, the SMT cannot unfold the definitions
through the append — even for concrete list lengths.

### The fix: explicit cons everywhere

Eliminate ALL `@` from both encode and decode. Use explicit `::` (cons) chains:

```fstar
(* BEFORE — SMT cannot chain through @ *)
let encode (bs: list byte) : list byte =
  match bs with
  | b0::b1::b2::rest -> [c0; c1; c2; c3] @ encode rest

let decode (bs: list byte) : option (list byte) =
  match bs with
  | c0::c1::c2::c3::rest ->
    (match decode_group ... with
     | Some bytes ->
       (match decode rest with
        | Some tl -> Some (bytes @ tl)))

(* AFTER — SMT can unfold everything directly *)
let encode (bs: list byte) : list byte =
  match bs with
  | b0::b1::b2::rest -> c0 :: c1 :: c2 :: c3 :: encode rest

let decode (bs: list byte) : option (list byte) =
  match bs with
  | c0::c1::c2::c3::rest ->
    (match decode_group ... with
     | Some bytes ->
       (match decode rest with
        | Some tl ->
          (match bytes with
           | [b0;b1;b2] -> Some (b0 :: b1 :: b2 :: tl)))
```

### Result

With cons-only encode/decode, roundtrip induction requires only:
- One group-content lemma per block size
- One recursive call (IH)

No structural lemmas (`encode_append`, `encode_expand`, `decode_unfold`) needed.
The SMT sees through the list structure directly.

### When to apply

Any verified codec, parser, or printer that concatenates encoded output with `@`.
Append is opaque to SMT; cons is transparent. Do NOT apply to list proofs using
`List.Tot.Properties` — those already have append lemmas.

### List Index Through Symbolic Prefix — `lemma_index_append_suffix`

**Critical lesson**:
SMT CANNOT normalize `L.index (l1 @ l2) i` where `l1` is symbolic
(even with a known length refinement).  `L.index` is opaque through `@`.

**The fix**: decompose the list into `l1 @ l2` where `l2` is a
**fully concrete** list (e.g., `[0x13uy;0x03uy;0x00uy]`), then use:

```fstar
let rec lemma_index_append_suffix (#a:Type) (l1 l2: list a) (k: nat {k < L.length l2})
  : Lemma (ensures L.index (l1 @ l2) (L.length l1 + k) == L.index l2 k)
    (decreases l1)
  = match l1 with | [] -> () | _ :: t -> lemma_index_append_suffix t l2 k

let rec lemma_index_append_prefix (#a:Type) (l1 l2: list a) (i: nat {i < L.length l1})
  : Lemma (ensures L.index (l1 @ l2) i == L.index l1 i)
    (decreases l1)
  = match l1 with | [] -> () | h :: t -> if i = 0 then () else lemma_index_append_prefix t l2 (i - 1)
```

**Pattern**: Build the body as explicit `l1 @ l2` segments where each
`l2` is concrete.  Call `append_length l1 l2` first to expose the
length, then `lemma_index_append_suffix l1 l2 k` to bridge to the
concrete byte.  SMT then normalizes `L.index [0x13uy;0x03uy;0x00uy] 0`
directly.

**Requirements**:
- `l1` needs a length refinement so SMT knows `L.length l1` (pass as
  `random: list byte {L.length random = 32}`)
- `l2` MUST be fully concrete (`[0x13uy; 0x03uy]`, not `p4 @ p5`)
- Call `append_length l1 l2` BEFORE the suffix lemma call (in the same
  SMT query if possible; `--split_queries always` may separate them)
- Works up to ~2 layers of symbolic prefix.  5+ layers of chained
  `append_length` + lemma calls exceeds SMT capacity

**Does NOT work for**: multi-layer nested `@` with symbolic segments
at every layer (e.g., `p1 @ random @ p3 @ pub @ p5`).  For those,
use `--admit_smt_queries true` and document the empirical validation
(test vectors, integration tests).

---

## 15. Codec Record Field Opacity Across Modules

**Critical lesson**: Codec record fields defined in
the codec library's types module have DIFFERENT transparency characteristics
when accessed from other modules.

| Field | Transparent? | Notes |
|---|---|---|
| `.enc` | YES | SMT can evaluate `c.enc v` and prove equalities about it |
| `.dec` | YES | SMT can evaluate `c.dec s` for concrete inputs |
| `.wfcv` | NO | Lambda in a `noeq type` record — SMT treats as uninterpreted |
| `.wfcv_prop` | NO | Same — opaque lambda, needs connector lemmas |
| `.rest_cond` | NO | Same — opaque lambda, needs connector lemmas |
| `.roundtrip` | NO | Lemma-typed field — requires clause uses opaque fields above |

### Consequence

You CANNOT call `addr_codec.roundtrip v Seq.empty` from another module and
expect SMT to discharge the requires clause. The requires clause references
`.wfcv`, `.wfcv_prop`, and `.rest_cond` which are ALL opaque. SMT cannot
prove them.

### Fix: the list-level proof pattern

Write explicit list-level encode/decode functions (no codec combinators),
prove roundtrip via direct structural induction, then bridge to the codec
via `lemma_codec_enc_eq_list` (which uses transparent `.enc` field).

```fstar
(* List-level roundtrip — proven by induction on the data structure *)
let lemma_addr_list_roundtrip (v: addr) : Lemma
  (decode_addr_list (encode_addr_list v) == Some (v, length (encode_addr_list v)))
  = ...

(* Bridge: encoder is transparent, so SMT proves this equality *)
let lemma_codec_enc_eq_list (v: addr) : Lemma
  (addr_codec.enc v == seq_of_list (encode_addr_list v))
  = ()

(* Final roundtrip: chain the bridge with the list-level proof *)
let lemma_roundtrip (v: addr) : Lemma
  (ensures addr_codec.dec (addr_codec.enc v ++ empty) == Inr (v, |enc v|))
  = lemma_addr_list_roundtrip v;
    lemma_codec_enc_eq_list v;
    lemma_seq_of_list_length (encode_addr_list v)
```

### `product` combinator internal assertions

The `product` combinator's `.roundtrip` field contains internal `assert`
statements about `c1.rest_cond` and `c2.rest_cond`. These pass at DEFINITION
time (where `c1`, `c2` are generic — SMT treats `c1.rest_cond` as
uninterpreted and the assertion passes vacuously). But at CALL time with
CONCRETE codecs, the assertions ARE checked and SMT cannot discharge them
because `.rest_cond` is opaque. The `--admit_smt_queries true` flag hides
this failure. The list-level pattern bypasses the entire combinator chain.

### ⚠️ Bridge lemma fragility — `()` body breaks across F*/Z3 versions

**Critical lesson**: The `()`-body bridge lemma above is
fragile.  Codecs built on it have broken silently when
F*/Z3 was updated — what passed at one rlimit fails at a much higher one.

**Why**: The `()` body asks SMT to normalize the entire combinator chain
(`byte_val` → `product` → `map_` → `digits_to_int`) and equate it to a
list-append chain.  Even though `.enc` fields are transparent, the chain
is deep and Z3 resource limits vary across versions.

**Fix: structural bridge proof**.  Decompose the encoder chain step by
step instead of relying on `()`:

```fstar
#push-options "--z3rlimit 400 --split_queries always"
let lemma_codec_enc_eq_list (v: addr) : Lemma
  (addr_codec.enc v == seq_of_list (encode_addr_list v))
  = let o0 = digits_encode (U8.v v.octet0) in
    let o1 = digits_encode (U8.v v.octet1) in
    let o2 = digits_encode (U8.v v.octet2) in
    let o3 = digits_encode (U8.v v.octet3) in
    let expected = seq_of_list (o0 @ [0x2Euy] @ o1 @ [0x2Euy] @
                                o2 @ [0x2Euy] @ o3) in
    assert (addr_codec.enc v == expected);
    ()
#pop-options
```

This breaks the problem into pieces (one `let` per octet).  For maximum
robustness, add `Seq.lemma_eq_intro` or `assert_norm` per combinator layer.

**Test after F* updates**: Run a full check after ANY toolchain update.
If rlimit needs bumping, the proof is drifting — add structural steps.

---

## 16. Fixed-Size Structure Pattern

For codecs with a FIXED number of fields (not recursive):

1. **Encode**: Use `digits_encode` / `encode_hex_group` directly (no `map_`,
   `product`). Concatenate with explicit structure (eventually `::` cons-only,
   see §14).

2. **Decode**: Use `digits_to_int_decode_go` / `decode_hex_group` directly.
   Write the decode function in `if None?` / `Some?.v` style — SMT can follow
   this better than nested `match` expressions:

```fstar
(* PREFERRED — SMT can follow explicit control flow *)
let decode (bs: list byte) : option (t & nat) =
  let step0 = decode_field1 bs in
  if None? step0 then None
  else
    let (v0, n0) = Some?.v step0 in
    let after0 = drop n0 bs in
    if length after0 < 1 || hd after0 <> 0x2Euy then None
    else ...

(* AVOID — nested match is opaque to SMT *)
let decode (bs: list byte) : option (t & nat) =
  match decode_field1 bs with
  | None -> None
  | Some (v0, n0) ->
    match ... with ...
```

3. **Roundtrip lemma**: Chain field-level roundtrips with explicit `assert`
   statements showing each intermediate `drop` / `hd` / decode result.

4. **Field-level roundtrip**: Call `lemma_digits_decode_encode_roundtrip`
   directly with the CORRECT `max_len` value (e.g., `3` for digits), NOT
   `digits_to_int.roundtrip` which has a shadowing bug (see §17).

---

## 17. `digits_to_int` Shadowing Bug and Workaround

### The bug

In the codec combinator library's types module, `digits_to_int` defines:

```fstar
let digits_to_int (n: pos) (f: int -> bool) : codec int = {
  ...
  rest_cond = (fun v r ->
    let n = nat_of_int v in              // SHADOWS the `n: pos` parameter!
    List.Tot.length (digits_encode n) = n \/  // BUG: compares length to VALUE
    Seq.length r = 0 \/                        // (should compare to max_len)
    (Seq.length r > 0 /\ not (is_digit (Seq.index r 0))));
  roundtrip = (fun v r ->
    let n = nat_of_int v in              // Same shadowing — both n's are the value
    lemma_digits_decode_encode_roundtrip f n n r;  // max_len=VALUE, n=VALUE
    ());
}
```

The `let n = nat_of_int v` shadows the `n: pos` parameter (max digit count).
This makes the first disjunct of `rest_cond` compare encoded length against
the VALUE (e.g., `3 = 255` — always false) instead of against `max_len`
(e.g., `3 = 3` — true when the encoding uses exactly max_len digits).

### When it matters

`digits_to_int.rest_cond n suffix` fails when `suffix` starts with a digit
and the encoded length doesn't happen to equal the value (which is almost
always). This is triggered inside `product` combinator chains when
a `digits_to_int` codec appears in a non-final position.

### Workaround

Call `lemma_digits_decode_encode_roundtrip` DIRECTLY with the correct
`max_len` value:

```fstar
(* CORRECT — max_len = 3, the actual max digit count *)
lemma_digits_decode_encode_roundtrip (fun v -> 0 <= v && v <= 255) 3 n r

(* WRONG — goes through digits_to_int.roundtrip which passes max_len=value *)
digit_codec.roundtrip n r
```

This bypasses the shadowing bug entirely. The direct lemma call uses the
correct `max_len` and its requires clause is provable when `r` starts with
a non-digit byte or is empty.

---

## 18. `noeq type` Record Field Opacity Across Module Boundaries

**Critical lesson**: When a `noeq type` record has
function-valued fields (lambdas) and is defined in module A, any code
in module B that accesses those fields sees them as **uninterpreted
functions**. SMT CANNOT evaluate them.

### The problem

A codec combinator library's types module defines:

```fstar
noeq type codec (a:Type) = {
  enc       : a -> Tot byte_seq;                    // lambda — opaque to SMT
  dec       : byte_seq -> Tot (decode_result a);    // lambda — opaque to SMT
  wfcv      : a -> Tot bool;                        // lambda — opaque to SMT
  wfcv_prop : a -> Tot prop;                        // lambda — opaque to SMT
  rest_cond : a -> byte_seq -> Tot prop;            // lambda — opaque to SMT
  roundtrip : (v:a) -> (r:byte_seq) -> Lemma ... ;  // lemma-typed — requires opaque fields
  ...
}
```

In a consumer module, calling `addr_codec.wfcv v` or
`octet_codec.rest_cond v r` results in SMT treating these as
uninterpreted functions.  The SMT solver cannot unfold them to
their definitions.

### Consequence 1: product.roundtrip internal assertions fail at call sites

The `product` combinator's `.roundtrip` field contains:

```fstar
assert (c1.rest_cond v1 (enc2 `Seq.append` r));
assert (c2.rest_cond v2 r);
```

These pass at DEFINITION time (where `c1`, `c2` are generic — SMT
sees `c1.rest_cond` as uninterpreted and the assertion passes
vacuously).  At CALL time with CONCRETE codecs (e.g., `octet_codec`),
the assertions ARE checked and SMT cannot discharge them.

Error:
```
Error 19: Assertion failed
```

### Consequence 2: assert_norm also cannot help

`assert_norm` computes closed terms at type-checking time, but it
also cannot normalize through `noeq type` record fields from other
modules.  Both SMT and the normalizer hit the same opacity barrier.

### Consequence 3: `--admit_smt_queries true` is the only local fix

Adding `--admit_smt_queries true` to the lemma that calls `.roundtrip`
admits the internal combinator assertions.  This is a SMT encoding
artifact, NOT a logical gap — the combinators were proven correct
at definition time.  Always pair with a 0-admit backstop proof
(list-level roundtrip via structural induction).

### The right fix: field-accessor lemmas in the defining module

Add lemmas to the codec library's types module that export the field
equalities:

```fstar
(** Lemma: product wfcv expands to conjunction.  Body is () because
    field equality is definitional within the defining module. *)
let lemma_product_wfcv_eq (#a #b:Type) (c1: codec a) (c2: codec b) (x: a) (y: b) : Lemma
  ((product c1 c2).wfcv (x, y) == (c1.wfcv x && c2.wfcv y))
  = ()

let lemma_product_rest_cond_eq (#a #b:Type) (c1: codec a) (c2: codec b) (v1: a) (v2: b) (r: byte_seq) : Lemma
  ((product c1 c2).rest_cond (v1, v2) r ==
   (c1.rest_cond v1 (c2.enc v2 `Seq.append` r) /\ c2.rest_cond v2 r))
  = ()
```

These have `()` bodies because the equality is DEFINITIONAL within
the types module.  Callers in other modules can then `assert`
with these lemmas — SMT can substitute the lemma-given equality
but cannot compute it directly from the field.

### Alternate fix: full manual combinator-chain unfolding

Without changing the types module, the only way to eliminate
admits is to fully bypass the combinator chain.  For each codec,
manually unfold:
- `.enc` — prove `addr_codec.enc v == seq_of_list (list_enc_v)`
  by decomposing `map_` → `product` → `byte_val` → `digits_to_int`
- `.dec` — prove `addr_codec.dec s == result_of_list_decoder (seq_to_list s)`
  by decomposing the same chain

This is the list-level pattern taken to its logical conclusion:
structural lemmas at every combinator layer.  Verbose but eliminates
ALL admissions without touching shared dependencies.

### Buffer-slice bridging for large fixed-size structures

For 16-element structures:
- SMT cannot chain 16 `Seq.lemma_index_slice` results into a single
  post-condition.  Write a custom induction lemma:
  ```fstar
  let rec lemma_slice_indices (s: Seq.seq U8.t) (off n: nat) (expected: list U8.t) : Lemma
    (requires off + n <= Seq.length s /\ n == List.Tot.length expected /\
              Seq.slice s off (off + n) `Seq.equal` Seq.seq_of_list expected)
    (ensures (forall (i: nat). i < n ==> Seq.index s (off + i) == List.Tot.index expected i))
    (decreases n)
  ```
- SMT cannot chain 16 `LB.upd` Stack post-conditions.  Group writes into
  4×4 chunks with an intermediate lemma, reusing the proven 4-byte
  pattern from a smaller corresponding lemma.

### Refined type inference in map_

When a record field has a refined type (e.g., `group = g:int{...}`),
the backward map in `map_` returns the refined type.  F* infers the
codec value type from the backward map, causing a mismatch if the
product codec uses the base type (`int`).

Error:
```
Expected type codec (group & ...)
got type codec groups_tuple (= codec (int & ...))
```

Fix: annotate the backward map's return type explicitly:
```fstar
(fun (ip: addr) : option groups_tuple ->
  Some(ip.group0, (ip.group1, (...))))
```

This tells F* to coerce each `group` to `int` (valid because
`group <: int`).  The forward map should include explicit range
checks when constructing the record from `int` values.

### Pulse `fn` `ensures` for a fixed-16-byte struct — POINTWISE, not `seq_of_list`

**Verified lesson (fstar-uuid, v2026.09.20 Custard/Pulse).**  The §11 "~12-layer"
Seq-unwind limit bites TWO ways in a `#lang-pulse` `fn` that reads/writes a fixed
16-byte record (e.g. an RFC 9562 UUID):

1. **The WRITE direction** — 16 `buf.(jN) <- byteN` produce a 16-deep `Seq.upd`
   chain in `pts_to`; an `ensures` of the form
   `Seq.slice s1 off (off+16) \`Seq.equal\` Seq.seq_of_list (encode16_spec u)`
   does NOT discharge at ANY `--z3rlimit` — it is opacity, not a resource
   shortfall (the full-build error shows all 16 `_s'NN == Seq.upd _s'MM …` steps
   in scope yet the final slice equality unproven).
2. **The READ direction** — `seq_to_list (slice s0 off (off+16))` does not reduce
   to the 16 elements because `s0` is a symbolic `Seq`.

**The fix that verifies 0-admit: make the `ensures` POINTWISE, with a refined
`noextract` reconstruction helper.**

```fstar
(* noextract reconstruction helper: the `off + 15 < Seq.length s` refinement
   makes each `Seq.index` term well-typed without a separate bounds lemma. *)
noextract
let uuid16_of_indices (s: Seq.seq U8.t) (off: nat { off + 15 < Seq.length s }) : uuid16 = {
  byte0 = Seq.index s (off + 0); ...; byte15 = Seq.index s (off + 15);
}

fn encode_uuid16 (u: uuid16) (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires A.pts_to buf s0 **
      pure (U32.v off + 16 <= A.length buf /\ U32.v off + 15 < 4294967296)
    returns w: U32.t
    ensures
      (exists* (s1: Seq.seq U8.t).
        A.pts_to buf s1 **
        pure (U32.v off + 16 <= A.length buf /\
              Seq.length s1 == A.length buf /\
              Seq.index s1 (U32.v off + 0) == u.byte0 /\
              ... /\ Seq.index s1 (U32.v off + 15) == u.byte15)) **
      pure (w == 16ul)
{ ... 16 writes ...; 16ul }

fn decode_uuid16 (buf: A.array U8.t) (off: U32.t)
    (#s0: erased (Seq.seq U8.t))
    requires A.pts_to buf s0 **
      pure (U32.v off + 16 <= A.length buf /\ U32.v off + 15 < 4294967296 /\
            A.length buf == Seq.length s0)   (* the length fact types the helper below *)
    returns r: opt_uuid16
    ensures A.pts_to buf s0 **
      pure (A.length buf == Seq.length s0 /\
            U32.v off + 16 <= A.length buf /\
            r == OU16_Some (uuid16_of_indices s0 (U32.v off), 16ul))
{ ... 16 reads ... }
```

Key points:
- The ENCODE `ensures` lists 16 `Seq.index s1 (off+N) == u.byteN` conjuncts, NOT
  a `Seq.slice == seq_of_list` equality.  Each conjunct is an independent
  write-and-read-back that SMT discharges (the Nth `Seq.index` of the `Seq.upd`
  chain is exactly the Nth write).
- The DECODE `ensures` states `r == OU16_Some (uuid16_of_indices s0 (U32.v off),
  16ul)`, and `uuid16_of_indices` carries the `off + 15 < Seq.length s0`
  REFINEMENT on its argument, so the term is well-typed without a separate
  bounds lemma.  The `requires` must also carry `A.length buf == Seq.length s0`
  (which `A.pts_to_len` establishes only inside the body) so the refinement
  discharges at the `ensures` typechecking point.
- This is the §18/§11 analogue ("16-element bridge") applied to the PULSE `fn`
  surface, not to a pure `Lemma`.  The pure `Lemma` induction
  (`lemma_slice_indices`, §18) is still the tool for pure-spec slice proofs;
  this pattern is the C-extractable `fn` analogue.
- The proven 4-byte ceiling (≤4 writes per `fn`, as in `Data.Codec.Pulse`'s
  `word32be`/`word32le`) has NOT been raised — the pointwise `ensures` is what
  makes 16 writes tractable, not a higher write count per se.

---

## 19. Open-Order Fragility — Export Behavior Across Module Boundaries

**Lesson**: Moving `open` statements can affect
qualified export behavior, but the effect is subtle and depends on
combinations of changes.  Isolate and test each change individually.

### What happened

In a module `Foo.Addr`, moving `open Foo.Base` to the top of the
file AND changing a constant's doc comment from `(** ... *)` to
`(* ... *)` (a regular comment) caused the constant to become
inaccessible via qualified module access.  Either change alone was
fine, but the combination broke export.

Later, changing the constant from `= 0x3Auy` to `: byte = 0x3Auy`
(with the proper `(** ... *)` doc comment) worked fine — the type
annotation alone does not break export.

### Revised lesson

- `open Foo.Base` at the TOP of a module is fine.
- `: byte` type annotation on a constant works.
- `open A.Types` is redundant when `open A` is already present (A
  re-exports A.Types).
- Always verify export behavior with the actual build command, not just
  a single-module check.
- Test each change individually — batch changes can interact in
  unexpected ways.

---

## 20. Multi-Field Record Refinement — Split-Function Pattern

**Critical lesson**: When a function returns a record with
many refined fields (16+), SMT cannot discharge all subtyping obligations
in a single query, even with `--split_queries always` and `--z3rlimit 300`.
The refinement chain through intermediate `let` bindings gets too deep.

### The problem

A key-schedule-like function returns `k: keys { 16 field-length refinements }`.
Each field is computed by a chain of opaque calls.  The return-type
refinements of `assume val` functions do not propagate through intermediate
`let` bindings in a way SMT can use for record construction.

### The fix: split into computation + construction

Separate the computation from the record construction.  The construction
helper takes all values with **explicit parameter refinements** — each
becomes an independent SMT subtyping query at the call site:

```fstar
(* Step 1: computation function — no return-type refinement needed *)
#push-options "--z3rlimit 300 --split_queries always"
let compute_keys (...) : Tot (k: keys { ... 16 refinements ... })
  = let k1 = ... in
    ...
    let k16 = ... in
    finish_keys k1 k2 ... k16  (* 16 independent subtyping queries here *)
#pop-options

(* Step 2: construction helper — parameters CARRY the refinements *)
let finish_keys
  (k1 : list byte {length k1 = 32})
  (k2 : list byte {length k2 = 32})
  ...
  : Tot (k: keys { ... 16 refinements ... })
  = { k1; k2; ... }  (* trivial — all refinements are in parameter types *)
```

### Why it works

When calling `finish_keys`, F* must verify that each argument matches
its refined parameter type.  With `--split_queries always`, each of
the 16 subtyping checks becomes an independent SMT query.  Inside
`finish_keys`, the body is trivial — the parameter types already
encode all the necessary refinements.

### Additional: extract nested calls

Calls like `derive_secret hs der_label (sha256 [])` lose the refinement
of `sha256 []` because it's nested in argument position.  Extract to
a `let` binding:

```fstar
let empty_hash = sha256 [] in             (* refinement: length empty_hash = 32 *)
let derived = derive_secret hs der_label empty_hash in  (* carries refinement *)
```

### When to apply

Any function returning a record with 8+ refined fields where each field
comes from a chain of calls to functions with return-type refinements.

---

## 21. Implicit Resolution Cascade — Fix-One-Thing Breaks Another

**Critical lesson**: When one module has a bug that masks
symbols (e.g., unclosed `(**` comment), fixing it can cause implicit
argument resolution failures in downstream modules that previously
depended on those symbols being absent or resolved differently.

### The cascade

1. Invariants.fst had an unclosed `(**` that swallowed `lemma_product_step_preserves_invariants`
2. The Integration.fst test bound that lemma via `open Invariants` —
   but since the symbol didn't exist, the binding failed silently at
   an earlier point in typechecking, which happened to constrain
   implicit `#e` type parameters on other bindings
3. When the comment was fixed and `lemma_product_step_preserves_invariants`
   reappeared, the typechecking order changed — now the earlier bindings
   (like `mk_mealy false (fun _ _ -> None)`) had their `#e` unconstrained,
   and the implicit resolution that previously "just worked" now failed
   with Error 66

### The fix: explicit type annotations at test boundary

At integration test boundaries where generic event types are abstract,
always annotate polymorphic helpers with explicit type parameters:

```fstar
(* BEFORE — fragile, depends on typechecking order *)
let _test_t_terminal : prop = terminal (mk_state_machine false (fun _ _ -> None)) false

(* AFTER — explicit #s #e prevents cascade *)
let _test_t_sm : state_machine_t bool unit = ...
let _test_t_terminal : prop = terminal _test_t_sm false
```

### Detection

When a seemingly-unrelated fix (comment closure, import removal) causes
Error 66 (implicit resolution) or Error 19 (subtyping) in a test module,
stop and type-annotate all generic helpers in the test — don't chase the
cascade through each individual binding.

---

## 22. Integration Test Bridge Lemma Bindings

**Lesson**: When binding Low* bridge lemmas in integration
tests, do NOT add explicit type annotations with weaker pre/post-conditions.
The annotated type will fail subtyping against the lemma's actual Stack type
(Error 19: refinement mismatch on requires/ensures clauses).

### The problem

```fstar
(* WRONG — typed annotation fails subtyping *)
let _test_low_encode_match_type
  : sm_state -> LB.buffer U8.t -> U32.t
  -> Stack unit (requires fun h0 -> True) (ensures fun h0 _ h1 -> True)
  = Foo.Low.lemma_encode_match
(* Error 19: refinement mismatch — the lemma's actual type has
   requires live h0 buf /\ offset < length buf *)
```

### The fix: admit SMT + untyped value binding

```fstar
(* CORRECT — let inference determine the type, admit the SMT at test boundary *)
#push-options "--admit_smt_queries true"
let _test_low_encode_match_type = Foo.Low.lemma_encode_match
let _test_low_decode_match_type = Foo.Low.lemma_decode_match
#pop-options
```

Let F* infer the full type (with all requires/ensures).  Admit the SMT
queries at the test boundary — the lemma is already proven in its defining
module; the integration test just needs to confirm the symbol exists.

The same pattern applies to any lemma with non-trivial requires clauses
that reference heap-dependent predicates at the integration test boundary
where no real buffer is available.

### Also required

Add `module U8/U32/LB` aliases and `open FStar.HyperStack.ST` in the
integration test module so the inferred Stack types resolve correctly.

---

## 23. The `reject` Codec Pattern — Functional Failure, Not Exceptions

**Lesson**: When a codec combinator needs to reject invalid
input (e.g., `n > max` in a length-prefixed list decoder), do NOT use
exceptions or `fail_` (which is an F* reserved keyword anyway).  Instead,
construct a codec whose `.dec` always returns `Inl`.

### The pattern

```fstar
(** A codec that rejects all inputs.

    Pure functional — no exceptions.  The decoder always returns [Inl],
    the encoder produces empty output for any value (unreachable since
    wfcv is false), and all validity predicates are false.

    @param reason Human-readable rejection reason.
    @returns A codec for any type [a] that rejects all inputs. *)
let reject (#a:Type) (reason: string) : codec a = {
  enc = (fun _ -> Seq.empty);
  dec = (fun s -> Inl ({ pos = 0ul; reason = reason }));
  wfcv = (fun _ -> false);
  wfcv_prop = (fun _ -> False);
  rest_cond = (fun _ _ -> False);
  roundtrip = (fun v r -> ());
}
```

### Usage with `bind`

```fstar
let event_codec (#e: Type) (max: nat) (ec: codec e) : codec (list e) =
  bind varint (fun n ->
    if n <= max then count n ec else reject "list too long")
```

`bind`'s decoder tries the inner codec.  When `n > max`, the inner codec
is `reject`, whose `.dec` immediately returns `Inl`.  No runtime exception —
the error propagates through the normal decode result path.

### Why not exceptions?

- F* codecs are total functions (`Tot`, not `Exn`)
- `fail_` is a reserved keyword in F* (see fstar-lang §11)
- Exceptions break extraction to C/OCaml/WASM
- The `reject` pattern is compositional — it works inside `bind`, `product`,
  `sum`, and any other combinator that calls `.dec` on a sub-codec

### Roundtrip

The roundtrip lemma has a vacuous body `()` because `reject.wfcv` is `false` —
the precondition is never satisfied, so the ensures holds trivially.

---

## 24. `Lemma (ensures True)` and `Lemma (True)` Antipatterns

### `ensures True` proves nothing

A lemma of type `Lemma (ensures True)` is **always provable** regardless of
what the body does.  The `()` body discharges trivially — True is true.
Such lemmas add zero formal verification and create a false impression of
proof.  They are documentation with lemma syntax.

```fstar
(* VACUOUS — always provable, proves nothing *)
let lemma_my_property () : Lemma (ensures True) = ()

(* EQUIVALENT — Lemma (True) desugars to Lemma (ensures True) *)
let lemma_my_property () : Lemma (True) = ()
```

### `requires P` with `ensures True` also proves nothing

Even with a nontrivial requires clause, `ensures True` means the lemma
conclusion is always satisfied.  The requires is just a precondition —
it doesn't become a proof obligation for the CALLER unless the ensures
actually asserts something:

```fstar
(* ALSO VACUOUS — requires carries no proof burden when ensures is True *)
let lemma_with_pre (x: int) : Lemma (requires x > 0) (ensures True) = ()
```

When a caller invokes `lemma_with_pre 5`, SMT must prove `5 > 0` — but
that's all.  The lemma then returns `()` with `True` as the postcondition.
No property about `x` is established.

### The `requires True` + `ensures True` extreme

`Lemma (requires True) (ensures True)` is the most vacuous form —
equivalent to `let _ = ()`.  It should never appear in production code.

### When `ensures True` IS acceptable

Per fstar-proofs §7 (Ghost/Stack Bridge), `ensures True` bridge lemmas
are acceptable ONLY when:
1. The requires clause carries a substantive proof burden that SMT
   must discharge at the call site (e.g., `requires B.live h buf /\
   U32.v off + 16 <= B.length buf`), AND
2. The lemma body calls other lemmas that chain through the requires
   to establish invariants for subsequent code.

The bridge lemma pattern is: the requires encodes what the caller must
prove; the `ensures True` acknowledges that the Stack effect prevents
SMT from expressing the real postcondition.  The real property is
tested at runtime.  But these lemmas should STILL have nontrivial
requires — never `requires True`.

### Specification skeleton pattern (aspirational, not proven)

A third legitimate use of `ensures True` / `Lemma (True)` lemmas is as
a **specification skeleton**: declaring the signature of a property that
SHOULD eventually be proved, with `()` as a "not yet implemented" stub.

These files MUST:
- Live in `docs/` (not `test/` or `src/`)
- Have a header: "SPECIFICATION SKELETON — these lemmas document
  properties to prove; bodies are `()` stubs. Real proofs TBD."
- Not be in the build path (Makefile `grep -v` filter)
- Not have integration test bindings

This pattern is for roadmap/design documents written in lemma syntax
so that type-checking validates parameter/return types unify, even
though the proof body is empty.  It is used for security properties,
loop invariants, and state machine refinements that are planned but not
yet implemented.

### `Lemma (True)` variant

`Lemma (True)` is syntactic sugar for `Lemma (ensures True)`.  Same
rules apply: acceptable only as a bridge lemma with nontrivial requires.

### Audit check

When reviewing F* code, flag every `Lemma (ensures True)` or
`Lemma (True)`:
- If `requires` is `True` or trivial AND the file is in `src/` → REMOVE
  (it proves nothing; if documenting intent, move to docs/ as spec skeleton).
- If `requires` is nontrivial and the lemma bridges Stack/Heap → KEEP
  but document the bridge pattern.
- If the file header says "NOT IN BUILD PATH" or "specification skeleton"
  → KEEP (it's aspirational documentation, not code).
- If the lemma is in `test/` with `ensures True` and no spec-skeleton header
  → EXTRACT to docs/ as a specification skeleton (preserve design intent).

---

## 25. `admit()`-Bodied Functions Are Dead Code

A function whose body is `admit()` has zero F* verification.  Any code
after the `admit()` in the same function body is never reasoned about
by F* — the function could return anything.

```fstar
(* DEAD CODE — the 80 lines after admit() are never verified *)
let parse_ch_key_share ... =
  admit();
  if ... then ...  (* F* never checks this — could be anything *)
```

### What to do

- If the function has no callers → REMOVE it entirely.
- If the function is a backward-compat wrapper and callers exist →
  declare it as `assume val` with only the type signature (no body).
- Never leave `admit()`-bodied functions in production `src/`.

---

## 26. Tautology Lemmas

A lemma that proves `P \/ ~P` (law of excluded middle) or any other
logical tautology adds zero information.  F* can already use excluded
middle through SMT.  Remove such lemmas:

```fstar
(* TAUTOLOGY — remove *)
let lemma_exhaustive (ct: byte) : Lemma (ct = handshake \/ ct <> handshake) = ()
```

Also applies to: `True`, `A ==> A`, `(A /\ B) ==> A`, and any
proposition that is definitionally true in F*.

### When `requires P` with `ensures True` IS vacuous

`Lemma (requires P) (ensures True)` proves nothing about P.
The requires clause gates the callsite — SMT must prove `P` at the
call — but the ensures is just `True`.  The lemma body contributes
zero logical content.  This is NOT a bridge lemma (which needs a
NONTRIVIAL requires that carries proof burden for subsequent code).

```fstar
(* ALSO VACUOUS — requires carries no proof burden when ensures is True *)
let lemma_with_pre (x: int) : Lemma (requires x > 0) (ensures True) = ()

(* Caller: SMT proves x > 0, lemma returns (), nothing is established *)
```

Only acceptable when the requires clause is itself the property being
documented (e.g., `requires U32.v result = 65` documents the expected
return code, but proves nothing).  In that case, prefer a doc comment
or a named constant — not a lemma.

## 27. `assume val` for External Library Properties

When a property is believed to hold of an external library (e.g., a
foreign crypto library)
but cannot be proven (no access to source, or proof is infeasible),
use `assume val` rather than a bare `admit()`-bodied lemma:

```fstar
(* CORRECT — honest about being an assumption *)
assume val lemma_p256_sign_output_len (result: U32.t)
  : Lemma (ensures U32.v result = 0 \/ U32.v result = 64)

(* WRONG — looks like a lemma but body is admit() — misleading *)
let lemma_p256_sign_output_len (result: U32.t)
  : Lemma (ensures U32.v result = 0 \/ U32.v result = 64)
  = admit()
```

`assume val` makes it explicit: this is an AXIOM, not a proven lemma.
Callers know they are relying on an unverified assumption.  A bare
`admit()`-bodied `let` looks like a lemma with an unfinished proof.

This applies to: foreign-library return code conventions, FFI type
isomorphism assumptions, and properties of opaque external functions where the
source is not available for verification.

---

## 28. Specification Skeletons — DO NOT put .fst files in docs/

Specification skeletons are aspirational lemma signatures intended as
design documentation for future proof work.  They do NOT belong in
the project `docs/` directory as `.fst` files — that creates confusion
about what is documentation vs code.

### The correct approach

1. **Proof patterns and recipes** → add to this skill file (fstar-proofs)
2. **Implementation-specific design notes** → write in markdown, keep
   in the package's `docs/` directory as `.md`
3. **Temporary proof work-in-progress** → keep in `test/` with an
   `assume` or admittance, marked clearly with a date and owner

### What to NEVER do

- NEVER create `.fst` files in `docs/` — they are neither documentation
  (`.md`) nor verified code (`src/`) nor test artifacts (`test/`)
- NEVER use `Lemma (ensures True)` as a documentation format — write a
  markdown file describing what you intend to prove, with a plain-text
  signature if needed

---

## 29. State Machine Refinement — Low* ↔ Pure Spec Mapping

When a Low* implementation mirrors a pure-spec state machine, define an
explicit refinement mapping as a pure function from Low* states to spec
states.  This makes the refinement relation verifiable by case analysis.

### Pattern

```fstar
type low_state =
  | LS_Init
  | LS_ClientHelloReceived
  | LS_FinishedReceived
  | LS_Established
  | LS_Error

let map_to_spec (s: low_state) : spec_state =
  match s with
  | LS_Init                -> Start
  | LS_ClientHelloReceived -> WaitFinished
  | LS_FinishedReceived    -> Established
  | LS_Established         -> Established
  | LS_Error               -> ErrorState
```

### Refinement lemmas

Each Low* transition refines a pure-spec step.  Prove by case analysis
on the Low* state, using the spec's `step` function:

```fstar
let lemma_ch_received_refines (s: low_state) (ch_data: Seq.seq U8.t) : Lemma
  (requires s == LS_Init)
  (ensures map_to_spec LS_ClientHelloReceived ==
           Some?.v (step (map_to_spec s) (ClientHelloEv (Seq.seq_to_list ch_data))))
  = ()
```

The `()` body works because the `requires s == LS_Init` forces the match
to a single case — SMT can compute both sides to the same value.

### Full refinement theorem

Chain the per-state lemmas into a theorem that the full handshake path
(Init → ClientHelloReceived → Established) refines the spec:

```fstar
let theorem_refinement (s0 s1 s2: low_state) (ch fin: Seq.seq U8.t) : Lemma
  (requires s0 == LS_Init /\ s1 == LS_ClientHelloReceived /\ s2 == LS_Established)
  (ensures
    map_to_spec s0 == Start /\ map_to_spec s2 == Established /\
    step (map_to_spec s0) (ClientHelloEv (Seq.seq_to_list ch)) == Some WaitFinished /\
    step WaitFinished (FinishedEv (Seq.seq_to_list fin)) == Some Established)
  =
  lemma_ch_received_refines s0 ch;
  lemma_fin_received_refines LS_ClientHelloReceived fin;
  ()
```

---

## 30. Wire-Format Conformance Proofs

When proving conformance of an implementation to a wire-format spec, use
the following lemma patterns.

### Constant matching

To prove that implementation constants match the spec constants, define a
lemma that asserts structural equality of each byte list:

```fstar
let lemma_all_labels_match_spec () : Lemma
  (label_a == spec_label_a /\
   label_b == spec_label_b /\
   label_c == spec_label_c /\ ...)
  = ()
```

### Header (AAD) conformance

To prove that an N-byte record header matches the spec, assert the
individual byte values:

```fstar
let lemma_record_header_matches (len: nat {len < 65536}) : Lemma
  (ensures
    List.Tot.length (record_header Content_data len) = 5 /\
    List.Tot.index (record_header Content_data len) 0 = 0x17uy /\
    List.Tot.index (record_header Content_data len) 1 = 0x03uy /\
    List.Tot.index (record_header Content_data len) 2 = 0x03uy)
  = ()
```

### Message framing

To prove a message/frame header has the correct form (type tag + length),
assert index values of the encoded message:

```fstar
let lemma_message_framing (body_a body_b: list byte) : Lemma
  (ensures
    List.Tot.index (encode_msg {kind = K_a; body = body_a}) 0 = 0x01uy /\
    List.Tot.index (encode_msg {kind = K_b; body = body_b}) 0 = 0x02uy /\
    length (encode_msg {kind = K_a; body = body_a}) = 4 + length body_a)
  = ()
```

### Length-field construction

To prove a length-prefixed construction has the correct byte length,
chain `append_length` lemmas:

```fstar
#push-options "--z3rlimit 40"
let lemma_length_prefixed_len
  (label: list byte {length label < 250})
  (context: list byte {length context < 256})
  (len: nat {len < 65536})
  : Lemma
    (ensures List.Tot.length (
       uint16_to_bytes len @
       [U8.uint_to_t (6 + length label)] @
       label_prefix @ label @
       [U8.uint_to_t (length context)] @ context)
     = 2 + 1 + 6 + length label + 1 + length context)
  =
  let open FStar.List.Tot.Properties in
  append_length (uint16_to_bytes len) ([U8.uint_to_t (6 + length label)] @ label_prefix @ label @ [U8.uint_to_t (length context)] @ context);
  append_length [U8.uint_to_t (6 + length label)] (label_prefix @ label @ [U8.uint_to_t (length context)] @ context);
  append_length label_prefix (label @ [U8.uint_to_t (length context)] @ context);
  append_length label ([U8.uint_to_t (length context)] @ context);
  append_length [U8.uint_to_t (length context)] context
#pop-options
```

Use `--z3rlimit 40` — each `append_length` call is an independent SMT
query; `--split_queries always` is implicit when chaining lemma calls.

---

## 30. Lemma `ensures` Clause Syntax — `==` not `=`, No Nested `let`

> **Note on numbering**: The previous §30 (Transcript Hash Conformance) and this
> section are distinct. This section follows from §29 (State Machine Refinement)
> and §30 (Transcript Hash Conformance). Sections §31-§35 follow this section.

**Critical lesson**: Inside a `Lemma (ensures ...)` clause,
equality must use propositional `==` (from `Prims`) not boolean `=`
(from `eqtype`). Boolean `=` triggers Error 168 (syntax error) because
F* parses `=` as a binder in type-level contexts.

Additionally, `let h = f x in ...` inside `ensures` is NOT valid F*
syntax — it's a term-level construct not a type/prop construct.
SMT can see `handshake_header ht body_len` directly without the
let-binding.

```fstar
(* WRONG — = and let h ... in cause Error 168 *)
let lemma_bad (ct: content_type) (pl: nat) : Lemma
  (ensures record_header ct pl =
           [content_type_to_byte ct; 0x03uy; 0x03uy; ...])
  = ()

let lemma_also_bad (ht: handshake_type) (body_len: nat) : Lemma
  (ensures
    let h = handshake_header ht body_len in
    L.length h = 4 /\
    L.index h 0 = handshake_type_to_byte ht)
  = ()

(* CORRECT — use == and reference the expression directly *)
let lemma_good (ct: content_type) (pl: nat) : Lemma
  (ensures record_header ct pl ==
           [content_type_to_byte ct; 0x03uy; 0x03uy; ...])
  = ()

let lemma_also_good (ht: handshake_type) (body_len: nat) : Lemma
  (ensures
    L.length (handshake_header ht body_len) == 4 /\
    L.index (handshake_header ht body_len) 0 == handshake_type_to_byte ht)
  = ()
```

Note: `=` works fine in `ensures` for simple value comparisons
(`ensures content_type_to_byte ct = 0x14uy`) because `U8.t` has
decidable equality and the type is simple.  The error only triggers
when `=` is used between two compound expressions (list literals,
function calls) where F* must distinguish `=` as a boolean operator
from `=` as a type-level binder.

Also: `append_length` returns `bool` (a proposition), not `unit`.
In a Lemma body, bind it with `let r = append_length ... in` —
bare `append_length ... ;` at the end produces Error 12.  In a `()`
body (SMT-dispatched), use `let r1 = append_length ... in let r2 = ... in ()`
pattern.

---

## 31. Assume-Val Lemmas — `()` Body Cannot Prove Cryptographic Properties

**Critical lesson**: When a lemma's ensures
clause involves `assume val` functions (e.g., a hash like `sha256`, a MAC
like `hmac`, a KDF, etc.), a `()` body CANNOT prove the property.  SMT
treats `assume val` functions as uninterpreted — it cannot reason about
their outputs.

### The problem

```fstar
(* VACUOUS — sha256 is assume val, SMT can't prove equality *)
let lemma_bad (a b: list byte) : Lemma
  (ensures sha256 (sha256 a @ b) == sha256 (a @ b))
  = ()

(* ALSO VACUOUS — hmac is assume val *)
let lemma_also_bad (key data: list byte) : Lemma
  (ensures compute_finished key data == hmac key data)
  = ()
```

SMT sees `sha256` as an opaque function symbol.  It cannot prove `sha256(X)
== sha256(Y)` for X ≠ Y, nor can it prove determinism of `hmac`.
The `()` body silently "proves" the lemma because SMT has no way to
DISPROVE it either — the function is uninterpreted.  This creates FALSE
confidence.

### The fix: `assume val` with test reference

Per fstar-proofs §27, declare properties that depend on `assume val`
functions as `assume val` themselves:

```fstar
(** Iterative hash construction.

    Since sha256 is [assume val], the iterative construction cannot
    be proven in F*.  Declared as [assume val] per fstar-proofs §27.

    Validated by: test_integration.
*)
assume val lemma_hash_iterative
  (prev msg1 msg2: list byte)
  : Lemma (ensures hash_append
             (hash_append prev msg1) msg2 ==
             sha256 (sha256 (prev @ msg1) @ msg2))
```

This is HONEST — it tells readers "this property is believed but not
proven; it is validated by named tests."

### When `()` IS safe with assume val

`()` is safe when the ensures is a DEFINITIONAL equality — both sides
reduce to the same term by function unfolding alone, without reasoning
about the opaque function's output:

```fstar
(* SAFE — definitional unfolding: sha256([] @ []) = sha256 [] *)
let lemma_empty_hash () : Lemma
  (ensures hash_append [] [] == sha256 [])
  = ()
```

### Audit check

When reviewing lemmas with `()` bodies, check every `assume val` function
in the ensures.  If the equality being asserted would require reasoning
about the function's output, flag as vacuous — change to `assume val`
with test reference.

### False associativity

The most dangerous variant: claiming a property that is MATHEMATICALLY
FALSE but SMT can't catch because the function is opaque.

```fstar
(* FALSE — sha256(sha256(A)||B) ≠ sha256(A||B) in general.
   But SMT can't tell because sha256 is opaque.  () body accepts it. *)
let lemma_false (prev msg1 msg2: list byte) : Lemma
  (ensures hash_append (hash_append prev msg1) msg2 ==
           sha256 (prev @ msg1 @ msg2))  // FALSE
  = ()
```

This kind of false lemma has been found in production — accepted for
months because SMT couldn't reject it.

---

## 32. Off-by-One in Byte-Level Spec Lemmas — Verify Against Source Layout

**Critical lesson**: When writing spec
compliance lemmas that check byte indices of constructed messages,
ALWAYS trace the field layout from the source function body.  Comments
like "offset 35 (2 + 32 + 1)" are misleading — [2 + 32 + 1 = 35] is
where the 35th field STARTS (0-indexed = byte 35), but each field may
span multiple bytes.

### The bug

A message body: `[0x03;0x03] @ random(32) @ [0x00] @ [0x13;0x03] @ ...`

| Bytes | Field |
|-------|-------|
| 0-1 | version |
| 2-33 | random (32 bytes) |
| 34 | id_length |
| 35-36 | cipher_suite |
| 37 | compression_method |

A lemma checking cipher_suite at body[34]=0x13, body[35]=0x03 was OFF
by one — body[34] is id_length (always 0x00), and the correct
indices are body[35]=0x13, body[36]=0x03.

### Prevention

For every byte-index lemma, include an ASCII layout table in the lemma's
fsdoc comment showing which byte indices correspond to which fields.
Verify against the actual `build_*` function body, not against mental
arithmetic.

Also: check existing lemmas before adding a new one that covers the same
byte range — a duplicate introduced the off-by-one here.

---

## 33. Cross-Module Buffer Layout Consistency — F* ↔ C Synchronization

**Critical lesson**: When F* Low* code and C
harness code share a buffer layout, changes to the layout MUST be
synchronized across `.fst` source, `.c` harness, and all documentation.

### The bug

A key-state layout in a Low* module was:
```
current_key[32] || previous_key[32] || timestamp[8] || prev_timestamp[8] = 80 bytes
```
But the C harness declared:
```c
static uint8_t g_key_state[48];  // STALE — only copies first 48 bytes
memcpy(out + 64900, g_key_state, 48);  // timestamps at offsets 64-71 never copied!
```
And another module documented:
```
(** [64900..64947] 48-byte key state *)  // STALE
```

This 3-way inconsistency went undetected through many review passes.
The C harness only copied 48 of 80 bytes, leaving timestamps at offsets
64-71 uninitialized.  Rotation comparisons read garbage timestamps.

### Prevention

1. **Single source of truth**: Document buffer layouts in exactly one place
   (F* source), reference from C via comment `// See Foo.Low.fst:NN`
2. **Sizes as named constants**: Use `#define KEY_STATE_SIZE 80` in C,
   `let key_state_size = 80ul` in F*, and cross-reference
3. **Audit checklist**: Every `memcpy` in C code MUST have a comment pointing
   to the F* source defining the layout being copied
4. **Integration test**: Copy known pattern to buffer, read back, verify roundtrip

---

## 34. `admit()`-Bodied Functions Mask Buffer Overflows

**Critical lesson**: When a function body starts
with `admit()`, F* performs ZERO verification of the function body.  Every
`B.upd`, `B.index`, `B.sub`, and `copy_bytes` call is unchecked.  Buffer
overflows that would be caught by F*'s refinement types in verified code
are invisible.

### The bug

Several encrypt/decrypt functions and their unit tests all had
`admit()`-bodied functions.  A field-size migration left
stale byte offsets in 15+ code sites.  F* never flagged any of them
because the bodies were never checked.

### Prevention

1. **Buffer layout comment**: Every `admit()`-bodied function MUST have
   an ASCII buffer layout table as a doc comment, showing every offset
   and what's stored there
2. **Offset audit on layout change**: When any field size changes, grep
   for all `B.upd`/`B.index`/`copy_bytes` calls in ALL modules, not just
   the one being changed
3. **Test the tests**: `admit()`-bodied unit tests MUST be runnable and
   MUST pass.  If they've never been executed, the test harness is broken
4. **Prefer `admit_smt_queries` over `admit()`**: An `admit_smt_queries`
   function still has its types verified (requires/ensures checked).
   A bare `admit()` skips everything.  Use `admit()` only at foreign-function
   FFI boundaries where the caller has no F* types for the foreign function

---

## 35. `open FStar.Mul` Is Required for Multiplication — Cache-Masked Bug

**Critical lesson**: In F\*, `*` defaults to the **tuple type
operator** (see fstar-lang §4).  For multiplication, you MUST `open FStar.Mul`
explicitly.  `open FStar.Mul` from an imported module is NOT transitive —
`open Some.Types` does NOT make `*` multiply in your module.

### The masked-bug mechanism

When building with `--cache_checked_modules`, F* loads `.checked` files for
transitive dependencies.  If a dependency module opens `FStar.Mul` and is loaded
from its `.checked` file, the cached environment carries the multiplication
interpretation of `*`.  This transitively infects modules that `open` it
even though `open` is not supposed to be transitive.  The result: `hi * 256 + lo`
works with a cached build but fails with a from-source check (which resolves
from source, not cache).

### Detection

```bash
# Find modules using * for multiplication without open FStar.Mul
grep -l '\* 256\|Prims.op_Multiply' src/*.fst | while read f; do
  grep -q 'open FStar.Mul' "$f" || echo "$f: MISSING open FStar.Mul"
done
```

### Fix

```fstar
open FStar.Mul  (* REQUIRED — * is tuple type without this *)
```

### Prevention

- Every module using `*` for multiplication MUST have `open FStar.Mul`
- CI: run a from-source check on every module (no cache masks)
- Run a full build with `--cache_off` periodically to flush transitive cache bugs
- Grep for `* <number>` in new code and verify `FStar.Mul` is opened

---

## 36. `*)` Inside `(**` Doc Comments — Premature Closure

**Critical lesson**: The sequence `*)` ALWAYS closes the
innermost open comment in F*, whether regular `(*` or doc `(**)`.  When
`*)` appears inside a `(** ... *)` doc comment, it prematurely closes the
comment, and everything after it becomes code.

### Common trigger patterns

- `visible to F*).` — the `*)` at `F*).` closes the doc comment
- `from Lib star),` — the `*)` at `Lib star),` closes the doc comment
- Any parenthetical containing a star followed by `)`

### Symptoms

- **No syntax error**.  The closed comment is valid syntax; subsequent prose
  becomes unparseable code.
- Error 168 (Syntax error) at a seemingly random line AFTER the doc comment
- Error 72 (Identifier not found) on what was prose text
- Symbols "disappearing" — the `*)` swallows source code as comment prose

### Fix

Reword to avoid `*)` inside any comment:
- `F*).` → `F star).`
- `Lib*),` → `Lib star),`
- `count(*)` → `count star close paren`

### Detection

Grep for `\*\)` inside `(**` blocks.  The python snippet:
```python
import re
text = open('Module.fst').read()
# Find (** ... *) blocks and check for *) inside them
for m in re.finditer(r'\(\*\*(.*?)\*\)', text, re.DOTALL):
    inner = m.group(1)
    if '*)' in inner:
        print(f'DANGER: *) inside doc comment at offset {m.start()}')
```

### Prevention

- Never write `*` followed by `)` inside any comment in F* source
- Treat `F*` as `F star` in all prose
- fstar-docs §8 covers the general pattern; this is the fsdoc-specific variant

---

## 37. `;` Before `#pop-options` in Stack Functions — Syntax Error

**Critical lesson**: In F*, `;` is the sequencing operator.
`e1; e2` means "evaluate e1, then e2".  The parser expects an expression
after `;`.  When the last expression in a Stack function body ends with
`;` and the next token is `#pop-options`, the parser sees
`expr; #pop-options` which is a syntax error — `#pop-options` is a
directive, not an expression.

### The pattern

```fstar
(* BROKEN — trailing semicolon before #pop-options *)
#push-options "--z3rlimit 20"
let my_function ... : Stack unit ... =
  ... body steps ...;
  last_step arg1 arg2;
#pop-options

(* FIXED — remove trailing semicolon *)
#push-options "--z3rlimit 20"
let my_function ... : Stack unit ... =
  ... body steps ...;
  last_step arg1 arg2
#pop-options
```

### Symptoms

- Error 168 (Syntax error) at the `#pop-options` line, column 12 (end of line
  for unindented `#pop-options`)
- The error line number points to `#pop-options`, not the semicolon — this is
  misleading because the actual bug is the trailing `;` on the previous
  expression line

### Detection

Grep for `;\n#pop-options` in F* source files (semicolon at end of line,
immediately followed by `#pop-options` on the next line).

### Why it matters

This was masked by `--cache_checked_modules` — the `.checked` files from a
full build with proper include paths hide the syntax errors.  Direct
LSP-based checks always catch it.

---

## 38. `if-then` Without `else` in `C.Loops.for` Callback Bodies

**Critical lesson**: A `C.Loops.for` loop body is a function
`Stack unit (requires ...) (ensures ...)`.  When the ENTIRE body is a bare
`if cond then expr` without `else`, F* reports Error 168 because the
function return type `Stack unit` requires both branches to produce `unit`.

### The pattern

```fstar
(* BROKEN — if-then without else is the entire function body *)
let body_loop (i: U32.t {0 <= U32.v i \/\ U32.v i < 32})
  : Stack unit (requires fun h -> inv h (U32.v i))
               (ensures fun _ _ h1 -> inv h1 (U32.v i + 1))
  = if not (U8.eq (B.index buf i) (B.index expected i)) then
      B.upd result 0ul 0uy

(* FIXED — add else () *)
let body_loop (i: U32.t {0 <= U32.v i \/\ U32.v i < 32})
  : Stack unit (requires fun h -> inv h (U32.v i))
               (ensures fun _ _ h1 -> inv h1 (U32.v i + 1))
  = if not (U8.eq (B.index buf i) (B.index expected i)) then
      B.upd result 0ul 0uy
    else ()
```

### When `else` is NOT needed

The pattern `if cond then expr; next_thing` IS valid because `;` sequences
to the next expression.  The `if` is part of a larger expression chain.

```fstar
(* VALID — semicolon chains to next statement *)
if U8.eq b0 0uy then B.upd result 0ul 0uy;
let computed_key = B.alloca 0uy 32ul in
...
```

### Symptoms

- Error 168 (Syntax error) at a line AFTER the loop body, often at a
  `#pop-options` or module-level doc comment
- The error position is misleading — the real bug is the missing `else`
  in the loop body function

### Detection

Grep for `= if .* then .*\n  in` or `= if .* then .*$` (without `else`
or trailing `;`) in Stack function bodies that are loop callbacks.

The 7 instances found in `Test.Integration.fst` were all `C.Loops.for`
callback bodies that did byte-by-byte comparison and set a result flag on
mismatch.

---

## 39. Proposal-Level Byte Index Errors — Verify Against the Actual Structure

**Critical lesson**: When auditing byte-index lemmas in a
proposal, verify indices against the ACTUAL build function body, not
against analogous structures from other messages.

### The false-positive

A proposal claimed a server-handshake lemma had an off-by-one bug
where the cipher suite was at bytes 37-38 instead of 35-36.  This was
WRONG — the auditor confused the server message (cipher_suite directly
at offset 35-36) with the client message (which has a `suites_len` field
before the cipher suites).

In `build_server_body`:
```
bytes 0-1:   version (0x0303)
bytes 2-33:  random (32 bytes)
byte  34:    id_len   (0x00)
bytes 35-36: cipher_suite     (0x1303)  ← CORRECT, no length field
byte  37:    compression      (0x00)
bytes 38-39: extensions_len
```

The server message has NO `suites_len` field — unlike the client message
where `cs_len = client_msg[cs_pos..cs_pos+2]`.  The cipher suite bytes are
directly in the server body.

### Prevention

1. **Trace the source function, not memory**.  Open the `build_*` function
   and count bytes from the first `[@]` or list cons.
2. **Include an ASCII layout table in the lemma's fsdoc** — this serves
   as the single source of truth for byte indices (fstar-proofs §32).
3. **Never analogize from another message type**.  Each message has its own
   wire format.  Two messages may share field names but differ in structure.
4. **When a proposal claims a bug, verify before implementing** — blindly
   applying false-positive findings would have broken correct lemmas.

## 40. Admit-Count Drift — Audit Procedure and Reliable Counting

**Lesson**: Admit counts drift across doc headers, task lists,
module `@header` comments, and the actual source.  A miscounted total
propagates to every derived goal.

### Why naive `grep -c 'admit'` lies

`grep -c 'admit'` counts MENTIONS, not code sites:
- doc-header prose ("Admit count: 16 code-site admit() calls")
- justification comments inside `(* ... *)` blocks
- `admit_smt_queries` (a different category) appears in `#push-options` lines
- the word "admission" / "admit" in prose

Counting code sites requires pattern disambiguation.

### Reliable patterns (per-module breakout)

```bash
# admit() code sites — matches the actual escape-hatch call
grep -c '= admit()\|push_frame(); admit()' Module.fst

# admit_smt_queries regions — count the #push-options lines (not the prose)
grep -c '#push-options .*admit_smt_queries true' Module.fst
```

The three admit() forms to catch:
1. `= admit();` — function body is just the escape hatch
2. `= push_frame(); admit();` — FFI-style wrapper
3. bare `admit();` (indented) — mid-function escape hatch, often at the
   top of a `(* ... *)` block that ends right before the call

### The audit procedure

1. Per-file `grep -n` of `admit()` and manually classify each hit:
   code site vs comment vs doc header.
2. Cross-check the doc `@header` count against the grep count.
3. Update the package-status table AND every task list that references the
   total in the same commit.
4. Recompute all derived goals — the running-total arithmetic must be
   consistent from the corrected baseline.

### Watch for these drift patterns

- **Double-count from a prior reconcile**: a doc says "8→9" or "11→10" but
  the net effect was never propagated to the totals.
- **Per-module sub-counts that sum to a different total than stated** — if
  the parts sum correctly but the header total is off, the header is wrong.
- **Lemma-count drift** in the same files (fstar-docs §9): use the same
  `grep -c '^let lemma_'` procedure and fix the header/table in the same commit.

---

## 41. `//` Line Comments Are Valid F* — Distinct From `///` Doc Comments

**Lesson**: F* accepts BOTH `(* ... *)` block comments
AND `//` line comments.  The lexer treats `//` to end-of-line as a comment,
just like C.  This is a common point of confusion when auditing:

```fstar
(* This is a valid F* block comment *)
// This is ALSO a valid F* line comment
let x : int = 1 // trailing line comment is valid too
```

### The `///` vs `//` distinction

A common documentation rule says "all `///` comments SHALL be converted to
`(** ... *)`".  That rule is about **triple-slash** `///` (the doc-comment
convention in some editors/languages), NOT about **double-slash** `//`.

```fstar
/// THIS is the doc-comment style that must be converted to (** ... *)
//  THIS is a regular line comment — valid and NOT subject to the (**) rule
type x = int
```

### Where `//` is idiomatic

Inline test-reference annotations on data elements are fine as `//`:

```fstar
let admit_inventory : list (string & string) = [
  ("helper_a", "composition"),  // test: test_suite_case_a
  ("helper_b", "composition"),  // test: test_suite_case_b
]
```

These are regular comments (carry no doc meaning, not surfaced by LSP hover),
so `//` is correct and `(** ... *)` would be over-verbose for per-element
annotations.

### Audit check

Do NOT flag `//` as a violation of the `///`→`(**)` rule.  Only `///`
(triple slash) requires conversion.  `//` is a legitimate line comment.

---

## 42. Stale `.checked` Files in `src/` Mask Bugs — Remove After Direct `fstar.exe` Runs

**Lesson**: Direct `fstar.exe` runs WITHOUT `--odir`
(or without `--cache_dir`) write `.checked` files into the SAME directory
as the source (`src/Module.fst.checked`) rather than the canonical
`out/checked/` location.  These stray `.checked` files are the cache-masking
hazard described in fstar-proofs §35, but they sit NEXT to the source where
they are easy to overlook.

### Detection

```bash
# Stray .checked files in src/ (gitignored, but stale)
ls src/*.checked 2>/dev/null
```

`.checked` files ARE gitignored (via `*.checked` in the root `.gitignore`),
so they never appear in `git status`.  This makes them invisible to the
standard "is my tree clean?" check — you must `ls` for them explicitly.

### Why remove them

1. **They mask syntax/name-resolution bugs** — a build with
   `--cache_checked_modules` loads the stale `.checked` file instead of
   re-checking the source, hiding errors introduced after the cache was
   written (e.g. a name-resolution bug).
2. **They are in the wrong location** — canonical location is
   `out/checked/`, so `src/*.checked` is always a sign of a stray build.
3. **They drift** — source edits do not invalidate them; the `.checked`
   content reflects an older source state.

### Safe removal (back up first)

```bash
mkdir -p /tmp/<pkg>-stale-checked-backup
cp src/*.checked /tmp/<pkg>-stale-checked-backup/ 2>/dev/null
rm src/*.checked
```

No commit is needed — the files are gitignored and regenerable.  But the
ACT of removal is part of "polish": a clean `src/` contains only `.fst`
files.

### Prevention

- Always pass `--odir out/checked` (or `--cache_dir`) to `fstar.exe` so
  `.checked` files land in the canonical gitignored location.
- Add `ls src/*.checked` to any polish/audit checklist.
- A from-source single-module check does NOT use `.checked` caches, so it is
  immune to this hazard — prefer it for individual-module verification.

## 43. Greedy in an Invertible-Syntax Codec — Bounded Greedy, Not Unbounded

**Critical lesson**: The invertible-
syntax `codec` contract is `roundtrip : dec (enc v ++ r) == Inr (v, Seq.length
(enc v))` — the decoder must consume EXACTLY `|enc v|` bytes, a length
DETERMINED BY THE VALUE, not by the input.  An **unbounded** greedy decoder
("consume until predicate fails", a GADT-era `many`) has no such
bound, so it is NOT a valid codec — its consumed length depends on the input
suffix, and it cannot satisfy the roundtrip except under a non-compositional
`rest_cond` (`r == Seq.empty`, see the single-value pattern).

The codec DOES admit **bounded** greedy — `digits_to_int max_len f` is the
canonical proof.  Its decoder `digits_to_int_decode_go f s max_len 0 0` consumes
digits until a non-digit but is bounded by `max_len` (`decreases k`, `k = max_len`).
The three ingredients that make bounded-greedy invertible:

1. **`enc v` is canonical/minimal** — `digits_encode v` has no leading zeros,
   exact digit count, no trailing ambiguity.
2. **`dec` is bounded** by a `max` parameter (or a delimiter), not merely
   "until predicate fails".
3. **`rest_cond` ties value + suffix** with the 3-disjunct shape:
   ```fstar
   rest_cond = (fun v r ->
     List.Tot.length (digits_encode v) = max_len \/   (* consumed the whole bound *)
     Seq.length r = 0 \/                              (* no suffix *)
     (Seq.length r > 0 /\ not (is_digit (Seq.index r 0))))
   ```

### The bounded-greedy template (for `text_chars`, `ows`, HTTP runs, etc.)

Any GADT-era `make_codec`/`many_codec max c` greedy site becomes:

```fstar
let run (max: nat) (pred: byte -> bool) : codec (list byte) = {
  enc       = fun bs -> seq_of_list bs;            (* canonical *)
  dec       = bounded-greedy scan stopping at max bytes OR non-matching; (* BOUNDED *)
  wfcv      = fun bs -> length bs <= max /\ for_all pred bs;
  wfcv_prop = fun bs -> length bs <= max /\ for_all pred bs;   (* prop form *)
  rest_cond = fun bs r -> length bs = max \/ Seq.length r = 0 \/ not (pred (Seq.index r 0));
  roundtrip = induction on bs (same shape as count_roundtrip_list / digits);
  ...
}
```

The `rest_cond`'s first disjunct ("encoded length == max") is what makes the
bounded greedy decoder stop exactly at `|enc v|` — the MAXIMUM bound forces
canonical encoding to be the full run, mirroring `digits_to_int` exactly.

### The two viable patterns and the trade-off

| Pattern | rest_cond | Invertible? | Composable via `product`? |
|---|---|---|---|
| `digits_to_int max_len` (bounded greedy) | 3-disjunct (max \/ empty \/ next non-match) | ✅ | ✅ (delimiter = "next byte non-match") |
| symbolic-anchor (`rest_cond = r == Seq.empty`) | `r == Seq.empty` | ✅ | ❌ (no following delimiter) |
| `count n c` (static count) | (fixed n) | ✅ | ✅ but `n` must be a compile-time constant |
| `many`/unbounded greedy | n/a | ❌ | ❌ |

**#3 (length-prefix) is BLOCKED**: `count n c` requires STATIC `n : nat`, so
"read length `n` from the wire, then `count n c`" needs a monadic `bind` (a
`Bind`/`length_count` primitive), which the record codec REMOVED and deferred as
future work (a `length_count` primitive, with a `custom` codec used in the
interim).

### Known F* gotchas hit while building these

- **`open FStar.Mul` is required** for `% 256` / `pow2 8 = 256` normalization.
  Without it, `UInt8.uint_to_t (int_of_char c % 256)` fails with
  `Error 19: expected uint_t UInt8.n (= byte) got nat` (cache-masked variant of
  §35 — `pow2` unfolds via `*`, which is the tuple operator without `FStar.Mul`).

- **Name collision**: `Codec.Types.string_to_bytes : string -> byte_seq`
  collides with a downstream `Text.Codec.string_to_bytes : string -> list byte`.
  Downstream modules that `open Codec` and REDEFINE `string_to_bytes` with
  a different return type get confusing `byte`/`nat` subtyping errors far from
  the real site.  Rename the downstream helper (`text_string_to_bytes`) and
  expose the public API as a thin alias.

- **F* char roundtrip**: `char_of_int (U8.v (uint_to_t (int_of_char c % 256))) == c`
  for ASCII `c < 128` is provable via `FStar.Math.Lemmas.small_mod (int_of_char c) 256`
  + `FStar.Char.char_of_u32_of_char c` (NOT `u32_of_char_of_u32` — the wrong direction
  silently fails).  The map-level string roundtrip needs a
  nested `list char` induction, NOT a `()`-body (`ensure True`).
  ⚠️ That induction is a `let rec`, and it hits the §44 re-verification blocker
  when a later roundtrip lemma calls it — see §44 for the workarounds.

- **Slice-recursive scan beats pos-based scan**: for the bounded greedy decoder,
  recurse on `FStar.Seq.Properties.tail input` (= `slice input 1 (length input)`,
  carrying `length > 0`) rather than `scan input pos` with
  `decreases (length input - pos)` — the latter needs a nested shift lemma SMT
  cannot chain; the former aligns with `list cons` induction and uses
  `append_slices` + `lemma_seq_of_list_cons`.

## 44. Recursive Lemma Re-verification Breaks `small_mod` at Call Sites

**Critical lesson**:
A **recursive** lemma (`let rec`) whose body calls `FStar.Math.Lemmas.small_mod
(int_of_char c) 256` (or any fact derived by unfolding a recursive predicate)
FAILS to re-verify the instant F* re-checks it when a LATER lemma in the SAME
module CALLS it.  The recursive requires predicate (`List.Tot.for_all` OR a
locally-defined `let rec all_ascii_ok`) is OPAQUE to SMT in the caller's
context, so `small_mod`'s `0 <= x < 256` precondition cannot be discharged
from `int_of_char c < 128` (which only follows from unfolding the recursive
predicate on a `cons` list).

**Symptoms**:
- The recursive lemma's body verifies perfectly when the module has NO
  later definition that references it.
- The instant a later `lemma_X_roundtrip` calls it, the error moves BACK to
  the recursive lemma's `small_mod`/`assert` line — even though that line
  already verified at definition time.
- `#restart-solver`, `--z3rlimit 2000`, `--split_queries always`, SMTPat
  unfold lemmas (`[SMTPat (for_all f (h::t))]`), and `for_all_mem` do NOT fix it.

**Root cause**: recursive functions/predicates (`let rec`) are opaque to SMT
across their own module's later re-encodings (fstar-proofs §2).  Neither
`List.Tot.for_all` (recursive) nor a hand-written `let rec all_ascii_ok`
unfolds its `cons` case in a polluted context.

**Consequence for F* char roundtrips**: proving `text_bytes_to_string
(text_string_to_bytes s) == s` for ASCII strings requires char→byte induction
(§43), and that induction MUST be a `let rec`.  If the roundtrip codec lemma
also lives in the same module as the scan lemmas, the recursive char lemma is
re-verified and blows up.

**Two viable workarounds (both verified in isolation, integration is the hard
part)** — ordered by preference:
1. **Isolate the recursive char roundtrip in a child module that touches ONLY
   PURE non-recursive `string -> list byte` / `list byte -> string` maps** (NOT
   `char_of_int`-based per-byte predicates).  The `char_of_int`/`char_of_u32`
   SMTPat family is the actual cross-module polluter (§18); a plain `map`-based
   `text_string_to_bytes`/`text_bytes_to_string` (marked `unfold`) is transparent
   across the boundary.  Bridge back ONLY the pure map equality.  The per-byte
   ASCII fact (`int_of_char c < 128`) should then be derived NON-recursively, or
   carried on an explicit `head: char` parameter so `small_mod` never relies on a
   recursive `for_all`/`memP` unfold.
2. **Make the requires NON-recursive**: encode the head predicate as an explicit
   `head: char` argument with `int_of_char head < 128 && pred head` directly in
   the `requires`, recursing on `tl` with the same explicit head-parameter shape.
   This removes `for_all`/`all_ascii_ok`/`memP` unfold from the `small_mod` path
   entirely.
3. **Last resort**: `assume val` (an honest axiom, §27) for the roundtrip lemma,
   backed by a unit test.  Never `admit()` in a body.

**Status**: this is an OPEN F* SMT limitation, not a proof gap.  The bounded-greedy
codec structure (§43) is correct; only the roundtrip lemma's SMT discharge is
blocked.  `assume val` (§27) at the roundtrip lemma is the honest fallback, NOT
`admit()` in the body, if a trade-off must be accepted — but prefer pushing the
char roundtrip into a genuinely separate, SMT-clean module and bridging only
pure `string -> list byte` maps (transparent, non-recursive) back.

## 45. `Inr` Payload Congruence Fails for Opaque `string` + `Seq.length (seq_of_list …)`

**Critical lesson**:
§44 workaround #1 (isolate the recursive char↔byte roundtrip in a clean child
module) DOES close the §44 blocker for the char induction itself.  But the
parent codec module then hits a SECOND SMT wall when proving the codec
`roundtrip` ensures: the goal is `dec (enc v ++ r) == Inr (v, Seq.length (enc v))`
with `v : string`, and the SMT solver refuses to substitute either (a)
`text_bytes_to_string bs == s` (a `string` equality from
`FStar.String.string_of_list_of_string`, an opaque primitive) or (b)
`m == Seq.length (seq_of_list …)` (an opaque `Seq.length` of `seq_of_list`, even
though `seq_of_list` carries the `{List.length l == length s}` refinement) into
the `Inr` / tuple constructor of `either decode_error (string & nat)`.

**Why bare-variable congruence works but this does not**:
`f x n == f y n` with `x == y` (both BARE string variables) discharges fine.
But `Inr (text_bytes_to_string bs, n) == Inr (s, n)` with
`text_bytes_to_string bs == s` does NOT — `text_bytes_to_string bs` is
`string_of_list (map f (map g (list_of_string s)))`, an OPAQUE complex term, not
a bare variable.  SMT cannot substitute a `squash (complex_term == s)` into a
constructor argument because it cannot normalize `complex_term` to `s`.

**Reproducibility is hypersensitive to SMT context pollution (§5)**: the exact
same roundtrip lemma body verifies at 0 errors in a MINIMAL module (the codec
library + child module + scan/dec/enc/wfcv/rest-cond + roundtrip), but fails in
the real text codec module once `crlf`/`sp` (which use `map_`, `product`,
`byte_val` combinators) and the `text_chars` `custom` call are added AFTER the
lemma.  The `custom` combinator's internal `roundtrip` field re-asserts
`wfcv v` / `wfcv_prop v` /\ `rest_cond v r` (§18 opaque `.wfcv`/`.rest_cond`),
and this re-verification of a later-defined combinator chain pollutes the SMT
context.

**Two independent friction points (do not conflate)**:
1. The roundtrip LEMMA body's final `Inr`-with-`string` congruence — needs the
   shape `assert (dec input == Inr (text_bytes_to_string bs, |bs|)); assert (...
   == Inr (s, |bs|)); assert (... == Inr (s, Seq.length (enc s))); ()` with each
   step a bare-variable substitution.  Verifies when the module is clean.
2. The `custom` combinator's internal asserts at the `text_chars` call site —
   the `custom.roundtrip` field body fires `assert (wfcv_custom v)` etc. and the
   complex `text_chars_rest_cond`/`text_chars_wfcv` arguments don't discharge
   under the combinator's default rlimit.

**CLOSED**.  The fix is a COMBINATION of three changes,
each independently necessary:

1. **Move `crlf`/`sp` into a child module** (the delimiters module) (§45
   workaround #2).  A `map_`/`product`/`byte_val` chain defined *after*
   `text_chars` in the same module pollutes the SMT context (§5) and breaks the
   `custom` roundtrip verification.  The codec must be a SINGLE combinator
   (`text_chars`); the delims go in their own module that downstream code opens
   directly.

2. **Prove `dec_consumed_bound` for real** — the original had a `()` body, but
   `n <= Seq.length input` for a bounded-greedy scan is NOT trivial.  Add an
   induction lemma `lemma_scan_consumed_le_len` (recurse on `|input| + max`,
   use `Seq.length (tail input) == Seq.length input - 1` in the matchable branch)
   and call it from `dec_consumed_bound`.  The `()` body silently fails the
   moment the module is otherwise clean (Error 19 at the empty body).

3. **`mk_char` gate on the EXACT `char_code` bound** (UTF-8 decoder):
   `FStar.Char.char_of_int` has argument type `i: nat{i < 0xd7ff \/ (i >= 0xe000 /\
   i <= 0x10ffff)}`.  Gate every `char_of_int` call with an `if cp >= 0 &&
   cp < 0xD7FF then ... else if cp >= 0xE000 && cp <= 0x10FFFF then ... else None`
   helper.  Using `cp < 0xD800` is WRONG — the refinement is `< 0xd7ff` (F*'s
   `char_code` excludes 0xD7FF by off-by-one), so only the exact `< 0xD7FF` bound
   discharges.  This is what lets `utf8_decode_one` avoid `magic ()` entirely.

**Result**: the text codec, its delimiters child module, and its UTF-8 child
module all verify at 0 admits / 0 magic.

**Why the `Inr`-with-`string` congruence worked after all**: the final part of
`lemma_text_chars_roundtrip` (`assert (dec input == Inr (text_bytes_to_string bs,
|bs|)); assert (... == Inr (s, |bs|)); assert (... == Inr (s, Seq.length (enc s)))`)
DISCHARGES in a single-combinator module.  The reported §45 failure was NOT the
final congruence — it was the `custom` call-site Error 19, caused entirely by the
`crlf`/`sp` pollution.  Isolating the delims removed the pollution and the
`custom.roundtrip` field's internal `assert (wfcv_custom v)` etc. then discharged
under `--z3rlimit 2000`.

## 46. `char_code` Off-by-One and the UTF-8 Char Roundtrip Recipe

**Critical lesson**: F*'s `FStar.Char.char_code`
and `char_of_int` use the bound `i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)`,
which is **off-by-one** from the Unicode-correct scalar-value bound
`i < 0xd800 \/ (i >= 0xe000 /\ i <= 0x10ffff)`.  The Unicode scalar value 0xD7FF
(the last code point before the surrogate range 0xD800–0xDFFF) is a VALID scalar
value but is EXCLUDED by F*'s `< 0xd7ff`.

**Consequence for a UTF-8 decoder** (`char_of_int cp`): you must gate on the
EXACT `char_code` bound, not the Unicode-correct one:

```fstar
(* WRONG — `cp < 0xD800` does not discharge `cp < 0xd7ff` when cp = 0xD7FF *)
let mk_char (cp: int) : option FStar.Char.char =
  if cp >= 0 && cp < 0xD800 then Some (char_of_int cp)
  else if cp >= 0xE000 && cp <= 0x10FFFF then Some (char_of_int cp)
  else None

(* RIGHT — matches FStar.Char.char_code exactly *)
let mk_char (cp: int) : option FStar.Char.char =
  if cp >= 0 && cp < 0xD7FF then Some (FStar.Char.char_of_int cp)
  else if cp >= 0xE000 && cp <= 0x10FFFF then Some (FStar.Char.char_of_int cp)
  else None
```

This `mk_char` gate is what lets `utf8_decode_one` avoid `magic ()` entirely —
every `char_of_int` sits behind an explicit validity branch, so the refinement
discharges without an admit.

**The UTF-8 encode→decode roundtrip proof recipe** (proved 0-admit):

1. Split into 4 per-byte-length lemmas (`lemma_utf8_{1,2,3,4}byte`), each
   `(requires int_of_char c in [range])` `(ensures utf8_decode_one (char_to_utf8 c)
   == Some (c, []))`.
2. In each body, use `FStar.Math.Lemmas.lemma_div_mod code (1 << shift)` to prove
   `code == shift * (code / shift) + code % shift` — the byte-reassembly identity.
3. Assert each encode byte's continuation-classification (`is_cont b ==
   U8.v b >= 0x80 && U8.v b < 0xC0`) so the decoder's guard branches resolve.
4. Conclude with `FStar.Char.char_of_u32_of_char c` — the one primitive that
   bridges `char_of_int (int_of_char c) == c` (NOT `u32_of_char_of_u32`, the
   wrong direction; see below).
5. Top-level `lemma_utf8_roundtrip` dispatches on `int_of_char c` with the 4
   ranges: `< 0x80`, `< 0x800`, `< 0x10000`, else (the 4-byte case covers
   `0x10000 .. 0x10FFFF`, which is automatic from `char_code`).

**Direction gotcha**: `FStar.Char.char_of_u32_of_char c : char_of_u32 (u32_of_char c)
== c` (char, then back).  `FStar.Char.u32_of_char_of_u32 c : u32_of_char (char_of_u32 c)
== c` (code point, then back).  For a decoder that reconstructs a code point from
bytes and must land on the ORIGINAL `c`, you want `char_of_u32_of_char` — the
wrong direction (`u32_of_char_of_u32`) silently fails to connect the reconstructed
code point back to `c` because the two are `char_of_u32 (u32_of_char c)` vs
`char_of_int (reconstructed_code)`, numerically equal but syntactically distinct.

**Overlong/surrogate/above-max rejection**: prove by concrete `()`-body lemmas on
literal byte lists — e.g. `utf8_decode_one [0xC0uy;0x80uy] = None` (overlong),
`[0xEDuy;0xA0uy;0x80uy] = None` (surrogate U+D800), `[0xF4uy;0x90uy;0x80uy;0x80uy]
= None` (above 0x10FFFF).  These normalize directly; no `admit` needed once the
decoder's leading-byte ranges (`0xC2..0xDF`, `0xE0..0xEF`, `0xF0..0xF4`) exclude
the overlong/above-max first bytes.

### F* doc-comment vs type discrepancy (the `0xd800` vs `0xd7ff` trap)

**Critical lesson**: `FStar.Char.fsti`'s DOC comment
says `char_code` is "not between 0xd800 and 0xe000" (Unicode-correct), but the
ACTUAL type refinement is `n: U32.t{U32.v n < 0xd7ff \/ (U32.v n >= 0xe000 /\
U32.v n <= 0x10ffff)}` — which is **off-by-one**: it uses `< 0xd7ff` (exclusive),
excluding U+D7FF, a VALID Unicode scalar.  The doc comment is WRONG (or
stale) relative to the enforced type.

**Consequence**: gate `char_of_int` on the ACTUAL type bound (`< 0xD7FF`), never
on the doc comment (`< 0xD800`).  Trusting the doc comment and writing
`cp < 0xD800` makes `char_of_int 0xD7FF` a type error (0xD7FF fails the real
refinement `i < 0xd7ff`).  Always confirm the bound against
`fstar/ulib/FStar.Char.fsti` SOURCE, not its prose.

**Build-time pinning pattern**: when a module's correctness depends on a
external-library bound (like `char_code < 0xd7ff`) that could change in a future
release, add a pinning lemma that FAILS to verify if the bound drifts:

```fstar
(* Fails loudly if F* widens char_of_int to accept 0xD7FF *)
let lemma_char_code_bound_pinned () : Lemma
  (ensures mk_char 0xD7FF == None /\ mk_char 0xE000 == Some (char_of_int 0xE000))
  = ()
```

If a future F* release makes `char_of_int 0xD7FF` legal, `mk_char 0xD7FF` becomes
`Some ...`, and the `== None` conjunct fails verification — a loud signal that the
documented limitation (U+D7FF unrepresentable) must be revisited.  This turns a
silent semantic drift into a build failure.  Prefer this over a prose-only
"documented limitation" note whenever the assumption is load-bearing.

### REC [2] surrogate-rejection lemmas must be `int`-level, not `char`-level

**Verified**: when enforcing a code-point exclusion set, the SURROGATE branch
is special.  A surrogate code point (e.g. `0xD800`) is NOT a representable
`FStar.Char.char` — the `char_of_int` refinement is `< 0xd7ff \/ (>= 0xe000 /\
<= 0x10ffff)`, so
`FStar.Char.char_of_int 0xD800` is a TYPE ERROR (Error 19, the refinement
cannot be discharged).  Therefore:

```fstar
(* WRONG — ill-typed: 0xD800 fails the char_of_int refinement *)
let lemma_reject_surrogate () : Lemma
  (valid_char (FStar.Char.char_of_int 0xD800) == false) = ()

(* RIGHT — state the surrogate exclusion at the CODEPOINT (int) level *)
let lemma_reject_surrogate () : Lemma
  (ensures valid_cp 0xD800 == false) = assert_norm (valid_cp 0xD800 == false)
```

Pattern: define the exclusion predicate at BOTH levels — `valid_cp : int ->
bool` (self-contained bounds, no dependency on another predicate so it can
sit beside the other char predicates) and `valid_char : char -> bool =
valid_cp (int_of_char c)`.  The surrogate vector is provable ONLY at the
`int` level; the controls/noncharacters (`#x1`, `#xFFFE`, …) ARE representable
`char`s so they can be stated at either level.

### Decimal-vs-hex char-ref rejection asymmetry

A char-reference-exclusion rejection through the FULL `char_ref.dec` chain
discharges with a bare `= ()` only for the DECIMAL branch, not the HEX branch.
Reason: `digits_to_int`'s decoder (`digits_to_int_decode_go`) carries its value
guard `f` INLINE (checks `f a` at each terminal boundary), so `&#1;` reduces in
one step.  The hex analogue (`hex_digits_to_int`) is built as a `custom` over
`hex_decode_go` which has NO `f` gate — its [.dec] decodes the digit run to the
raw `int` and only the enclosing `map_` forward map (`mk_char`) rejects.  That
`map_`-over-`custom`-over-`between` reduction is opaque (fstar-proofs §15/§18),
so the noncharacter rejection must be stated at the GATE level
(`is_valid_cp 0xFFFE == false /\ mk_char 0xFFFE == None`), matching the
existing `lemma_char_ref_reject_surrogate`/`_above_max` pattern — NOT through
`char_ref.dec (seq_of_list [&#xFFFE;])`.

## 47. Second-Order `Lemma` Parameter in a `let rec` → "incomplete quantifiers"

**Critical lesson**: A `let rec` lemma (or
function) with a **`Lemma`-typed higher-order parameter** produces a
SECOND-ORDER quantified SMT goal that Z3 reports as `unknown because
(incomplete quantifiers)` — regardless of rlimit or fuel.  This is DIFFERENT
from (and was confused with) the opacity of mutually-recursive `let rec ... and`
predicates (§2).

### The two distinct quantifier sources (do not conflate)

1. **Mutually-recursive `let rec ... and ...` predicates** (e.g.
   `element_wf`/`node_wf`/`children_wf`) — opaque SMT symbols.  FIXED by
   de-mutualization: make ONE function the FUEL-indexed self-recursion and
   pass the "other" checker as a **plain function VALUE** (first-order).
   This WORKS — after de-mutualization, `node_wf fuel n` / `children_wf
   (node_wf fuel) ns` typecheck and UNFOLD cleanly under `--z3rlimit 80`.

2. **A `(fe: nat) -> (e) -> (suffix) -> Lemma (requires ..) (ensures ..)`
   parameter** (the "element_rt" pattern) passed into `let rec
   lemma_children_roundtrip` — a SECOND-ORDER function argument.  When the
   recursive equation is SMT-encoded, the `forall element_rt.` quantifies over
   a function that itself carries a `Lemma` (a `requires`/`ensures`), so Z3
   cannot instantiate it to discharge the post-condition.  NO amount of
   `--fuel`/`--ifuel` (tried 8/8) or `--z3rlimit` (tried 2000, uses only ~30)
   or `--split_queries always` closes it — the goal is genuinely undecidable
   ("incomplete quantifiers" with near-zero rlimit consumption, NOT "canceled"/
   timeout).

### How to recognize the second-order case

`--query_stats` shows `failed {reason-unknown=unknown because (incomplete
quantifiers)} ... rlimit 2000 (used rlimit ~30.0)` — the tiny `used rlimit`
vs the large `rlimit` is the tell: it is NOT under-resourced, it is
undecidable.  Contrast with a real timeout (`unknown because canceled`, used
rlimit ≈ rlimit).

### The workaround hierarchy (for mutually-recursive AST roundtrips)

A tree type `element ⇄ children(list of node) ⇄ element` has an INHERENT
mutual recursion.  The two encodings both break:
- `let rec ... and ...` → opaque (§2).
- higher-order VALUE param → second-order (#2 above).

Neither is SMT-decidible for the roundtrip post-condition.  The known-viable
paths are: (a) hand-write a single fuel-indexed self-recursion that does NOT
need to call the sibling lemma at the SAME fuel (requires the sibling fuel to
also decrease — not the case for a sibling list, where the element decoder is
held at a CONSTANT fuel across siblings); or (b) prove the CONCRETE vectors by
bounded `assert_norm`/`norm` (fuel = the small concrete depth, not the
`element_fuel = 1024`), dropping the general recursive lemma.  Prefer (b) for
user-facing roundtrip lemmas over a small test suite; keep the general lemma
as a documented `assume val` (#27) ONLY as a last resort — never `admit ()` in
a body.

### Path (b) empirical findings

Three VERIFIED facts refine path (b):

1. **Fuel-bridge DOES discharge.**  For a CLOSED example `ex` of depth `d`,
   `node_enc element_fuel (Element ex) == node_enc d (Element ex)`
   (with `element_fuel = 1024`) VERIFIES as a `()`-body lemma under
   `#push-options "--fuel 16 --ifuel 4"`.  The recursion is STRUCTURALLY
   `d` deep (it stops at text/empty leaves), so SMT unfolds ~`d` steps even
   though the fuel VALUE is 1024 — the fuel is just arithmetic, not a
   structural-unfold cost.  So bridging the large production fuel to the
   small concrete depth is NOT the blocker.

2. **The roundtrip itself does NOT discharge by fuel alone.**
   `element_dec d (node_enc d (Element ex) @ []) == Some (ex, [])` FAILS
   as a `()` body even at `--fuel 16 --ifuel 4`.  Matching the DECODED
   structure back to the original requires more than unfolding — it needs the
   leaf-lemma chain + structural reasoning SMT cannot do autonomously.

3. **`@` (list append) opacity (§14) blocks the MANUAL unroll.**  The
   element encoder/decoder (`element_body_enc`/`children_enc`/`children_dec`)
   are written with `@`-append (`nb @ (0x3E :: (children_enc ... @ close))`),
   and SMT cannot match a manually-constructed `body` against the encoder's
   `@`-chain (§14: append is opaque, cons is transparent).  So the manual
   step-by-step roundtrip (`assert (node_enc ... == <manual bytes>);
   leaf_lemmas`) FAILS at the very first encoding equality.  **The fix is to
   REWRITE `element_body_enc`/`children_enc` (and mirror `children_dec`) in
   CONS-ONLY form (§14), after which the manual unroll (or even `norm`) can
   compute the closed roundtrip.**  This is the concrete next step for path
   (b).

Net: the production combinator codec carries its roundtrip proof in
`.roundtrip` (0-admit, nix-verified); the list-level mirror's user-facing
roundtrip lemma needs the cons-only rewrite of the encoder/decoder before the
bounded-computation proof can close.

### Path (b) RESOLUTION — CONFIRMED, corrects findings #2/#3

The resolving session PROVED the four concrete vectors at 0 admits / 0 magic /
0 assume, with the full build GREEN.  The prior findings need two
CORRECTIONS and one ADDITION:

- **CORRECTION to finding #3 (cons-only is NOT required).**  The `@`-based
  `element_body_enc`/`children_enc` NORMALIZE FINE for CONCRETE closed terms:
  `assert_norm (node_enc d (Element ex) == [0x3C;…])` discharges for the
  empty/paired/nested vectors WITHOUT a cons-only rewrite.  §14's append
  opacity applies only to SYMBOLIC prefixes, not to closed literals — the
  normalizer unfolds `@` over a concrete left side directly.  (A cons-only
  rewrite attempt with inner `let rec go` to rebuild the list produced
  Warning 242 — inner let-rec not SMT-encoded — and was ABANDONED.)

- **CORRECTION to finding #2 (decode needs leaf lemmas, not just fuel).**
  The decode reconstruction fails on OPQUE `string` equality (§45):
  `text_bytes_to_string [0x61uy] == "a"` does NOT normalize, so
  `element_dec d [bytes] == Some (ex, [])` needs
  `lemma_text_string_to_bytes_roundtrip pred "a"` (which chains
  `FStar.String.string_of_list_of_string`) called for EVERY string
  in the vector, plus `assert_norm (text_string_to_bytes "a" == [0x61uy])` to
  fix the encode side.

- **ADDITION — `@ []` does not reduce in [ensures].**  The concrete lemmas'
  [ensures] uses `element_dec element_fuel (… @ [])`, and `@ []` has NO
  automatic reduction.  Add `List.Tot.Properties.append_l_nil (node_enc
  element_fuel …)` at the top of the body.

- **ADDITION — remove the dead WF/depth predicates.**  Once the general lemma
  is dropped, [node_wf]/[node_depth]/[children_wf]/[no_adjacent_text] are dead
  code AND pollute the SMT context (§5/§44) enough to break the otherwise-
  working empty-element lemma.  DELETE them.

- **ADDITION — LSP is looser than the full build.**  The `{text}` lemma
discharged under `--ifuel 8` via an LSP check, but needed `--ifuel 16` under
the real build.  Use `--fuel 32 --ifuel 16 --z3rlimit 400 --split_queries always`
for ALL four concrete lemmas.

**The complete working recipe (per vector `ex` of depth `d`):**
```fstar
#push-options "--fuel 32 --ifuel 16 --z3rlimit 400 --split_queries always"
let lemma_x_roundtrip () : Lemma
  (ensures element_dec element_fuel (node_enc element_fuel (Element ex) @ []) == Some (ex, []))
  =
  List.Tot.Properties.append_l_nil (node_enc element_fuel (Element ex));     (* @ [] in ensures *)
  assert (node_enc element_fuel (Element ex) == node_enc d (Element ex));  (* fuel bridge *)
  assert_norm (node_enc d (Element ex) == [/* literal bytes */]);             (* encode → literal *)
  lemma_text_string_to_bytes_roundtrip pred "a";  (* one PER string, name + text *)
  assert_norm (text_string_to_bytes "a" == [0x61uy]);
  assert (element_dec d [/* literal bytes */] == Some (ex, []));                 (* decode literal *)
  assert (element_dec element_fuel [/* literal */] == element_dec d [/* literal */]); (* decode bridge *)
  ()
#pop-options
```
Note the GENERAL recursive lemma is genuinely abandoned (NOT `assume val` — it
is dropped entirely); the concrete vectors carry the user-facing guarantee.

---

## 48. Delimiter-Aware Content Scans — the Flat Byte-Level Scan DOES Verify

**Verified lesson**: A codec whose
content is delimited by a multi-byte close marker the content may PARTIALLY
contain (comment `<!--…-->`, CDATA `<![CDATA[…]]>`, PI `<?…?>`), IS expressible
as a FLAT byte-level scan — and that scan VERIFIES at 0 admits, for all three
comment/CDATA/PI, in a single module.

Earlier drafts (§44/§48 as originally written, and the §49 atom reframing) were
WRONG.  Two independent errors in the earlier work:

1. **The comment well-formedness predicate omitted the trailing-`-` case.**  The
   scan stops at `--`, so content ending in a lone `-` merges with the close
   marker `-->`'s leading `-` to form a spurious `--`, truncating the content.
   The correct predicate rejects a trailing `-` AND any `--` (RFC `[15]`
   `((Char - '-') | ('-' (Char - '-')))*` — a `-` must be followed by a
   non-`-`, so it cannot be trailing).  With the trailing-`-` rejection, the
   comment scan discharges.
2. **The PI atom-draft used `c <> '?'`, but the correct single-char constraint
   is `?` followed by non-`>`** (RFC `[16] (Char* - (Char* '?>' Char*))` — `?>`
   is forbidden, but `??` is legal).

### The working pattern (all three, 0-admit)

The scan returns `(content, remaining)` and stops at the delimiter; the
well-formedness predicate is a simple recursive [*_ok] that the scan unfolds in
lockstep (the [text_chars]/[lemma_scan_prefix] structure), and the roundtrip
lemma states its result against a CONCRETE literal close marker:

```fstar
(* Comment: stop at `--`; forbid `--` AND a trailing `-` *)
let rec comment_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | [0x2Duy] -> false              (* trailing `-` *)
  | 0x2Duy :: 0x2Duy :: _ -> false  (* `--` *)
  | _ :: tl -> comment_ok tl
  | [] -> true

let rec scan_comment (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | 0x2Duy :: (0x2Duy :: _) -> ([], bs)   (* stop at `--` *)
  | b :: rest -> let (c, r) = scan_comment rest in (b :: c, r)
  | [] -> ([], [])

let rec lemma_scan_comment_exact (content: list byte) (r: list byte)
  : Lemma (requires comment_ok content == true)
          (ensures scan_comment (content @ [0x2Duy;0x2Duy;0x3Euy] @ r)
                    == (content, [0x2Duy;0x2Duy;0x3Euy] @ r))
          (decreases content)
  = match content with | [] -> () | b :: tl -> lemma_scan_comment_exact tl r
```

CDATA (stop `]]>`, predicate rejects only `]]>`) and PI (stop `?>`, predicate
rejects only `?>`) are structurally identical — no trailing guard for either
(a content ending in `]`/`]]` or `?` merges to `]]]`/`??`, which do NOT match
their stop sequences).

### Why the original §44/§48 experiments failed

They used [no `--`]-only predicates (missing the trailing-`-` case), so the SMT
step at `b :: tl` could not rule out the spurious boundary `--`.  Once the
predicate is RFC-correct, the induction is the ordinary [text_chars]/
[lemma_scan_prefix] walk and SMT discharges it.  **Do NOT reach for the §49
atom reframing — it is unnecessary.**

> **⚠️ Rule (combinator-only parsing).**  Even though the flat LIST-level scan
> verifies, production parsing should be a `codec a` combinator, never a bespoke
> `list byte -> option …` scanner.  The correct deliverable is a new codec
> primitive (`take_until delim content_ok max : codec string`) whose scan is
> BOTH list- AND seq-level; the open work is proving the SEQ-level roundtrip of
> that scan (the multi-byte `delim` lookahead does not yet discharge against the
> opaque `Seq` constructor, §11).  The list-level recipe above is the PROOF
> SKELETON for that combinatorial scan, not a delivered parser.

---

## 49. Atom-Level Reframing for Delimiter-Aware Content (SUPERSEDED — see §48)

> **⚠️ SUPERSEDED.**  This technique was developed as
> a workaround for the failure described in the OLD §48 ("flat scan does not
> verify"), but that failure was itself caused by an INCORRECT well-formedness
> predicate (missing the comment trailing-`-` case).  The flat byte-level scan
> DOES verify once the predicate is RFC-correct (see the CORRECTED §48).  Do
> NOT use this atom reframing for delimiter-aware content — it is unnecessary
> and, for CDATA, actually over-restricts to reject legal `]]` runs.
> Retained below for historical reference only.

**The technique** (historical) that was once thought to close the §48 blocker: when a content
language is a sequence of atoms each of which is locally well-formed (e.g.
comment content `((Char - '-') | ('-' (Char - '-')))*` — each atom is a
non-`-` char OR a `-` immediately followed by a non-`-` char), model the
content as a `list atom`, NOT a flat `list byte` with a `contains_*_delim`
guard.  Well-formedness becomes ELEMENTWISE over the atom list, which SMT
unfolds per-constructor — the exact structure `text_chars`'s `lemma_scan_prefix`
proves (`List.Tot.for_all (byte_matchable pred)`) versus the opaque
crossing predicate `not (contains_comment_delim bs)`.

### The pattern

```fstar
(* atom: PlainChar c (c <> '-') | DashChar c (c <> '-') *)
type comment_atom =
  | PlainChar : char -> comment_atom
  | DashChar  : char -> comment_atom

(* injective atom -> byte list encoding *)
let encode_atom (a: comment_atom) : list byte =
  match a with
  | PlainChar c -> [char_to_byte_trunc c]
  | DashChar  c -> [0x2Duy; char_to_byte_trunc c]

(* elementwise well-formedness over the ATOM list (not the bytes) *)
let atom_ok (a: comment_atom) : bool =
  match a with
  | PlainChar c | DashChar c -> ascii_ok (fun _ -> true) c && int_of_char c <> 0x2D

let rec atoms_ok (atoms: list comment_atom) : Tot bool (decreases atoms) =
  match atoms with
  | [] -> true
  | a :: tl -> atom_ok a && atoms_ok tl

let rec atoms_encode_bytes (atoms: list comment_atom) : Tot (list byte) (decreases atoms) =
  match atoms with
  | [] -> []
  | a :: tl -> encode_atom a @ atoms_encode_bytes tl

(* the scan: decide Plain vs Dash by the head byte; a '-' head consumes two *)
let rec scan_atoms (bs: list byte) : Tot (option (list comment_atom & list byte)) (decreases bs) =
  match bs with
  | [] -> Some ([], [])
  | 0x2Duy :: rest ->
      (match rest with
       | c :: tl ->
         if byte_matchable (fun _ -> true) c && int_of_char (byte_to_char c) <> 0x2D then
           (match scan_atoms tl with
            | Some (ats, r) -> Some (DashChar (byte_to_char c) :: ats, r)
            | None -> None)
         else None   (* '-' at end, or '- -' : invalid *)
       | [] -> None) (* trailing '-' : invalid *)
  | b :: tl ->
      if byte_matchable (fun _ -> true) b && int_of_char (byte_to_char b) <> 0x2D then
        (match scan_atoms tl with
         | Some (ats, r) -> Some (PlainChar (byte_to_char b) :: ats, r)
         | None -> None)
      else None

(* roundtrip: DISCHARGES by induction on the ATOM list *)
let rec lemma_scan_atoms_roundtrip (atoms: list comment_atom)
  : Lemma
    (requires atoms_ok atoms)
    (ensures scan_atoms (atoms_encode_bytes atoms) == Some (atoms, []))
    (decreases atoms)
  = match atoms with
    | [] -> ()
    | a :: tl -> lemma_scan_atoms_roundtrip tl
```

This lemma VERIFIES at 0 admits (proof-of-concept `Probe.fst`),
where the flat-byte `lemma_scan_comment_content_exact` with `not
(contains_comment_delim content)` FAILED across ~27 formulations.

### Why it works

- The `atom_ok` check is ELEMENTWISE over `atoms` (each constructor checks its
  own `char`), so `atoms_ok` unfolds per-constructor exactly as `text_chars`'s
  `for_all (byte_matchable pred)` does.
- The scan decision (Plain vs Dash) is a SINGLE head-byte lookahead that
  matches the constructor, not a 2-byte crossing predicate.
- The trailing-`-` rejection is STRUCTURAL: a trailing `-` cannot be a `DashChar`
  (it has no following char), so `scan_atoms` returns `None` on it — the
  well-formedness constraint is an atom-shape fact, not a separate predicate.

### The string↔atom bridge (next step for the codec)

The AST carries a `string`, so the codec also needs a proven bijection
`string ↔ list comment_atom` (chars to atoms).  This is the remaining piece to
wire the comment codec together: prove `scan_atoms (text_string_to_bytes s)
== Some (atoms, [])` and `text_bytes_to_string (atoms_encode_bytes atoms) == s`
for the valid `s`, using the existing `lemma_text_string_to_bytes_roundtrip` /
`lemma_chars_roundtrip_all` (the string↔bytes bridge).
CDATA uses an analogous atom (`PlainChar c`, `BracketChar c` rejecting `]]>`),
and PI an atom rejecting `?>`.

### When to apply

Any delimiter-aware content whose RFC production is a sequence of locally-
well-formed atoms (`Comment`, `CDSect`, `PI`, and any "`X*` minus a forbidden
subsequence" where the forbidden subsequence is expressible as an atom-shape
constraint).  This is the RECOMMENDED replacement for the flat
`contains_*_delim` + `lemma_scan_*_content_exact` pattern of the earlier §48
draft, which does not verify.

---

## 50. Delimiter-Aware Content Is a LIST-Level Operation — NOT a Seq-Level `codec`

**Supersedes §48's "flat scan DOES verify" follow-up and §49's atom reframing
for the *delivery* decision.**  The three content productions (comment `-->`,
CDATA `]]>`, PI `?>`) roundtrip at 0 admits at the **plain `list byte` level**
with a FLAT recursive scan whose stop condition is a literal-prefix pattern
match; the roundtrip lemma is a plain §48 structural induction on the content
list.  Verified for all three in one module.

### The finding

A design originally wanted `take_until` as a new `codec`
combinator in the codec types module.  That is the WRONG
primitive, because:

1. `codec.dec : byte_seq -> decode_result a` forces the scan over `FStar.Seq`.
2. A multi-byte delimiter lookahead does NOT reduce through the opaque `Seq`
   constructor — even `Seq.index (seq_of_list [0x61uy;0x3Fuy]) 0 == 0x61uy`
   fails for a CLOSED literal (not just symbolically).  Confirmed via four
   independent probe formulations (generic scan, `not_prefix` helper,
   `lemma_bytes_decode_no_prefix`, `no_self_overlap` precondition).
3. The bridging fact a list→Seq plan needs,
   `seq_to_list (seq_of_list l ++ s) == l ++ seq_to_list s`, was ORIGINALLY
   recorded as §11-unprovable, but it IS provable 0-admit via the transparent
   internal stdlib bridges (`lemma_seq_to_list_of_list_append` in the codec
   types module) — see §11 REVISED and §60.  This CORRECTION is what lets the
   list-level scan be wrapped as a `custom` codec with an arbitrary-suffix
   (general-`r`) roundtrip (§60).

### The correct pattern (already proven in-tree)

Delimiter-aware leaf content is a **list-level** operation, exactly like
The canonical example (which already proves the recursive `xml_element`
⇄ `xml_node` AST at 0 admits via list-level `node_enc : fuel -> xml_node ->
list byte` and `element_dec : fuel -> list byte -> option (xml_element &
list byte)` + bounded computation, §47 path b).  The deliverable is:

```fstar
(* content-validity predicates: reject ONLY the forbidden subsequence *)
let rec comment_ok (bs: list byte) : bool =
  match bs with
  | [0x2Duy] -> false              (* trailing `-` — RFC [15] *)
  | 0x2Duy :: 0x2Duy :: _ -> false  (* `--` *)
  | _ :: tl -> comment_ok tl | [] -> true

let rec scan_comment (bs: list byte) : (list byte & list byte) =
  match bs with
  | 0x2Duy :: (0x2Duy :: _) -> ([], bs)   (* stop at `--` prefix of `-->` *)
  | b :: rest -> let (c, r) = scan_comment rest in (b :: c, r)
  | [] -> ([], [])

let rec lemma_scan_comment_exact (content r: list byte) : Lemma
  (requires comment_ok content == true)
  (ensures scan_comment (content @ [0x2Duy;0x2Duy;0x3Euy] @ r) == (content, [0x2Duy;0x2Duy;0x3Euy] @ r))
  (decreases content)
  = match content with | [] -> () | b :: tl -> lemma_scan_comment_exact tl r
```

CDATA (`scan_cdata`, stop at `]]>`, `cdata_ok` rejects only `]]>`) and PI
(`scan_pi`, stop at `?>`, `pi_ok` rejects only `?>`) are structurally
identical; the comment is the only one needing the trailing-`-` guard.
All three + their `lemma_scan_*_exact` roundtrips verify at **0 admits / 0
assumes / 0 magic** (the `(_ok == true)` [requires] carries the guard; the
scan unfolds the predicate in lockstep — §48).

### The lesson (why the multi-byte lookahead is fine at list level, not Seq)

The list scan's stop check is a NON-NESTED constructor pattern (`0x2Duy ::
(0x2Duy :: _)`) over a TRANSPARENT `list`; the induction's head case is a
plain cons, so the SMT solver sees `comment_ok (b::tl)` unfold and the peek
discharge.  The Seq scan's equivalent check (`Seq.index s 0 = d /
Seq.index s 1 = d`) is a nested `Seq.index` over the OPAQUE `Seq` constructor,
so the same induction does NOT discharge (§11) — even after exposing index 0
and 1 via `lemma_seq_of_list_cons` + `append_assoc` + `append_slices` (a
`lemma_head_two` that DOES verify; the failure is in connecting the two-byte
peek back to the recursive `tail` reassembly across the `++ delim ++` knot).

### When to apply

Any delimiter-terminated content (comment/CDATA/PI, and any `X* - forbidden`
production): implement the scan + well-formedness predicate at the `list byte`
level and carry its roundtrip as a structural-induction lemma with a
`requires content_ok content == true` clause.  **Never** reach for a
Seq-level `codec` combinator (a `take_until`) for this — the opaque `Seq`
abstraction forbids the multi-byte-lookahead roundtrip.  The list-level + fuel
+ §47-path-b machinery is the canonical delivery vehicle; it is NOT a shortcut
— it is the only 0-admit way to consume a multi-byte delimiter over `byte_seq`
in F*.

---

## 51. Wiring Delimiter-Aware Leaf Nodes into a Fragile Recursive Decode — Isolation + the Rejection-Lemma Gap

**Verified lesson**: Landing
the three list-level leaf scans (§50) into the recursive element
`node_enc`/`children_dec` of an element codec exposes TWO distinct
pitfalls, both distinct from the §47 bounded-computation strategy they build
on.

### Pitfall 1 — INLINE `<`-dispatch breaks the nested element roundtrip

Adding the comment/CDATA/PI branches INLINE in [children_dec] (a `let rec`
over fuel) breaks the already-proven nested element roundtrip lemma
[lemma_element_nested_roundtrip], even though the nested vector contains NO
comment/CDATA/PI (so the new branches are dead for that input).  SMT still
encodes every added `else if c = 0x21 …` / `else if c = 0x3F …` branch into
each unfold step of the recursive [children_dec], which inflates the bounded-
computation decode assert past reach (Error 19 "Assertion failed" at the
decode assert).  Increasing `--ifuel` (16 → 32 → 64) makes it WORSE (the
query diverges, memory grows to GBs, "incomplete quantifiers" — §47), it does
NOT close it.

**The fix that works**: extract the special-node decode into a SINGLE helper
[dec_special_node : list byte -> option (xml_node & list byte)] and have
[children_dec] dispatch on it in ONE place:

```fstar
else if c = 0x21uy || c = 0x3Fuy then
  (match dec_special_node (b :: tl) with
   | None -> Some ([], bs)
   | Some (node, rest0) -> … recurse …)
```

This keeps [children_dec]'s body FLAT (three `<`-cases: close / special /
element) and the comment/CDATA/PI matching hidden inside [dec_special_node],
which SMT only unfolds when the `<` byte is actually [0x21] or [0x3F].  The
nested element lemma then verifies at `--fuel 64 --ifuel 32 --z3rlimit 800`
(up from `--fuel 32 --ifuel 16 --z3rlimit 400`).

**Combined with §44/§45 isolation**: the `let rec` `lemma_scan_*_exact`
roundtrip lemmas must ALSO stay OUT of the production leaf module — they live
in a TEST module, because opening a module that exports `let rec` lemmas into
the element codec module pollutes its SMT context (§44) and breaks the same
concrete roundtrip lemmas.  This was verified empirically: `open`-ing the leaf
module (with its lemmas, zero usage) ALONE hangs the element module's
verification.

### Pitfall 2 — the decoder's REJECTION property is incidental, not proven

The `*_ok` well-formedness predicate ([comment_ok]/[cdata_ok]/[pi_ok]) is the
SPEC of well-formedness and is the `requires` clause of the roundtrip lemma —
it names the ACCEPT side.  The DECODER ([dec_special_node]) does NOT invoke
`*_ok`; it rejects malformed content INCIDENTALLY: [scan_*] stops early at
the first forbidden-prefix (`--`, `]]>`, `?>`) and then the close-token
exact-match (e.g. `0x2D :: 0x2D :: 0x3E :: after`) FAILS, returning [None].
Traced for all three leaves, this DOES reject every malformed input (interior
`--`/`]]>`/`?>` and trailing `-`), so the decoder is correct — but there is
**no formal soundness/rejection lemma** stating `dec_special_node <malformed>
== None`.  The roundtrip lemma proves only the accept side.

**CLOSED**: the rejection lemmas are landed and verified —
`lemma_dec_comment_rejects_double_dash` / `_cdata_rejects_truncated_close` /
`_pi_rejects_truncated` in the test module, each `dec_special_node <malformed>
== None` proven by a concrete vector (a `()` body suffices — the node-level
decoder is non-recursive, so the malformed vector normalizes directly).  This
turns the incidental rejection into a stated, verified property, matching the
"rejection lemma" column of a lemma-coverage table.

### When to apply

Any time a delimiter-aware leaf scan (§50) is wired into a fuel-indexed
recursive decode whose roundtrip is proven by §47-path-b bounded computation:
(1) isolate the special-node dispatch in ONE non-recursive helper, never
inline multi-branch dispatch into the `let rec` decoder; (2) keep the `let rec`
roundtrip lemmas in a TEST module, never in a production module that the
recursive proof module opens; (3) budget a `--fuel`/`--ifuel` increase for the
concrete roundtrip lemmas after wiring; (4) pair every accept-side roundtrip
lemma with a concrete rejection/soundness lemma for the malformed inputs.

## 52. New Base-16 Codec — `custom` Not a Raw Record, Offset-Recursion Bound Lemmas

**Verified lesson**: Building a
new bounded-greedy digit codec (the hex analogue of `digits_to_int`) exposes
three pitfalls, all distinct from the decimal case (which reuses the
already-proven `digits_to_int`).

### Pitfall 1 — a raw record codec breaks `map_`/`between` composition (§18)

Defining `hex_digits_to_int` as a plain `{ enc; dec; wfcv; …; roundtrip }`
record (mirroring `digits_to_int` verbatim) makes its `.wfcv`/`.rest_cond`/
`.roundtrip` fields OPAQUE lambdas to the `map_`/`between`/`alt` combinators.
When `char_ref_hex = map_ … (between (text "&#x") (byte_val 0x3B) hex_digits_to_int)`
is later given a concrete roundtrip lemma, `map_.roundtrip`'s internal
`assert (c1.wfcv …)` / `assert (c1.rest_cond …)` cannot discharge — the
sub-codec fields are opaque (§18 Consequence 1), and the lemma fails with
Error 19 pointing INTO the combinator library's types module (the
combinator's internal assert), NOT at the new code.

**Fix**: build the new codec via **`custom`** (fstar-proofs §23, the
`text_chars` pattern), whose `.roundtrip` field calls YOUR explicit
`roundtrip_custom` lemma rather than re-asserting sub-combinator fields:

```fstar
let hex_digits_to_int (max_len: pos) (f: int -> bool) : codec int =
  custom
    (hex_decode max_len)                            (* dec *)
    (fun v -> seq_of_list (hex_digits_encode (nat_of_int v)))  (* enc *)
    (hex_digits_wfcv max_len f)                      (* wfcv *)
    (fun _ -> True)                                  (* wfcv_prop *)
    (hex_digits_rest_cond max_len f)                 (* rest_cond *)
    (fun v r -> lemma_hex_digits_roundtrip max_len f v r)
    (lemma_hex_dec_err_bound max_len)
    (lemma_hex_dec_consumed_bound max_len)
```

### Pitfall 2 — bound lemmas must recurse on the OFFSET, not slice the input

Naive `dec_consumed_bound`/`dec_err_bound` that recurse by slicing
`Seq.slice s 1 (Seq.length s)` and `decreases %[max_len; Seq.length s]` fail
under the full build's tight rlimit with "Assertion failed" at the recursive
call — SMT cannot chain `Seq.length (slice s 1 …) == Seq.length s - 1` through
the opaque `Seq` (§11).

**Fix**: mirror the standard `digits_decode_go_len_bound` lemma shape exactly —
recurse on `k` ONLY, carrying an explicit offset `i` (never slicing `s`):

```fstar
#push-options "--z3rlimit 200 --split_queries always"
let rec lemma_hex_decode_go_len_bound (s: byte_seq) (k: nat) (a: int) (i: nat) : Lemma
  (requires i <= Seq.length s)
  (ensures (match hex_decode_go s k a i with
            | Inr (_, n) -> n <= Seq.length s
            | Inl err -> err.err_pos <= Seq.length s))
  (decreases k)
  = if k = 0 then ()
    else if i >= Seq.length s then ()
    else begin
      let b = Seq.index s i in
      if is_hex_digit b then begin
        assert (i + 1 <= Seq.length s);
        lemma_hex_decode_go_len_bound s (k-1) (a * 16 + hex_digit_value b) (i+1)
      end
      else ()
    end
#pop-options
```

`dec_consumed_bound` = `fun s -> lemma_hex_decode_go_len_bound s max_len 0 0`.
The `assert (i + 1 <= Seq.length s)` is the single index-bound fact SMT needs.

### Pitfall 3 — LSP-green new codecs are NOT full-build-green; the concrete roundtrip lemma must chain, not `()`

A new codec's concrete roundtrip lemma (`char_ref_hex.dec (char_ref_hex.enc 'A')
== Inr ('A', …)`) LSP-verifies with a `()` body, but FAILS under the real
build `fstar.exe --z3rlimit 80` with "post-condition not proved".  The `()` body
asks SMT to normalize the whole `map_`/`between`/`hex_decode_go` chain, which
does not reduce the `hex_decode_go` recursion.

**Fix**: give the lemma an EXPLICIT body that chains the transparent
`.dec`/`.enc` fields (§15) through the list-level roundtrip facts — NEVER call
the opaque `.roundtrip` field, and NEVER `assert_norm` the `.enc` byte literal
(also opaque):

```fstar
let lemma_char_ref_hex_roundtrip () : Lemma
  (ensures char_ref_hex.dec (char_ref_hex.enc 'A') == Inr ('A', Seq.length (char_ref_hex.enc 'A')))
  = let code = FStar.Char.int_of_char 'A' in
    assert (code == 0x41);
    lemma_acc_hex_encode 0x41;
    lemma_all_hex_digits_encode 0x41;
    lemma_hex_decode_encode_roundtrip max 0x41 (seq_of_list [0x3Buy]);
    lemma_mk_char_of_char 'A';
    assert_norm (hex_digits_encode 0x41 == [0x34uy; 0x31uy]);
    assert (hex_decode max (Seq.append (seq_of_list [0x34uy;0x31uy]) (seq_of_list [0x3Buy])) == Inr (0x41, 2));
    ()
```

For REJECTION (`char_ref … <surrogate> == Inl`), the `char_ref.dec` + `()` body
does NOT discharge even at `--z3rlimit 2000 --fuel 32 --ifuel 32`.  State the
rejection at the gate instead: `lemma_char_ref_reject_surrogate () : Lemma
(is_valid_cp 55296 == false /\ mk_char 55296 == None)` with an `assert_norm
(is_valid_cp 55296 == false)` body — the `is_valid_cp`/`mk_char` code-point gate
IS the soundness property (§46), and it normalizes directly.

### When to apply

Any new bounded-greedy digit/run codec added outside the codec library's types
module (hex, base64, UUID, etc.): (1) build it with `custom`, never a raw
record; (2) prove its bounds with the offset-recursion
`lemma_*_decode_go_len_bound` shape; (3) prove concrete roundtrips by chaining
the list-level roundtrip lemmas through `.dec`/`.enc`, not `()` and not the
opaque `.roundtrip`; (4) prove rejections at the predicate/mk_char gate, not
the full `.dec` chain; (5) re-verify under the full build (LSP is looser).

---

## 53. Multi-Byte Prefix Choice Is a Combinator Composition, Not a Hand-Written Scanner

**Lesson**: A decoder that must disambiguate on a byte AFTER a shared
multi-byte prefix (e.g. two alternatives that share the leading bytes and only
diverge on a later byte) MUST be built from the combinator layer, not a
hand-written `seq -> decode_result` scanner.  Two recurring mistakes follow
from ignoring this.

### Mistake 1 — hand-writing a `seq` scanner with `index`/`slice` peek

A hand-rolled decoder that reads `index s 0`, `index s 1`, then `slice s 2 …`
to decide a branch does NOT discharge: the `slice`-of-`append` bridging
(`slice (prefix ++ rest) k … == rest` for a SYMBOLIC `rest`) is opaque across
module boundaries (see §11 and §50).  Raising the SMT rlimit does not help; the
equality is not a resource problem, it is invisible to the solver.  Rewriting
with more `assert` scaffolding also does not help — the `slice`/`append` knot
is the blocker, not the surrounding proof.

### Mistake 2 — duplicating a literal set to satisfy one-byte dispatch

If the only way to make a one-byte choice primitive dispatch correctly seems to
be "make a second copy of the literal set with the common prefix stripped", that
is a sign the prefix should have been FACTORED, not copied.  Two copies of the
same constant literals drift independently and each needs its own proof.

### The fix — factor the shared prefix, then compose

Strip the common prefix with a `then_drop`/`between`-style combinator so the
byte that actually disambiguates is the FIRST byte of the remaining inner
codec, then a one-byte choice primitive dispatches on it directly:

```
branch_a : parse/pre-print of the inner left alternative   (* first byte already distinct *)
branch_b : parse/pre-print of the inner right alternative
whole    = collapse-over-either (canonical backward map)
             (prefix-then (choice branch_a branch_b (predicate on the FIRST byte)))
```

Concretely, for a set of terminated literals that share a one-byte prefix, keep
ONE definition of the post-prefix body and derive the full form by prepending
the prefix combinator — do not keep a "with prefix" copy and a "without prefix"
copy side by side.

### Checklist (before writing any multi-byte-prefix-dispatched decoder)

1. Write the combinator composition first over the proven primitives.  Do NOT
   hand-write `dec`/`enc` over `seq`/`byte_seq` for a shared-prefix choice.
2. If two branches share a literal prefix, FACTOR the prefix with a `then_drop`/
   `between`-style combinator; do not duplicate the literal set.
3. Prove the concrete roundtrip by chaining the LEAF roundtrip lemmas of the
   inner digit/run/terminated-literal codec, not a bare `()` body — a one-byte
   choice over an inner combinator adds enough SMT work that `()` does not
   discharge under a tight rlimit (§52 Pitfall 3).
4. Re-verify under the real build (full-package verification), not just LSP —
   LSP is looser (§52).

---

## 54. `custom` Codec Fields Are Opaque Cross-Module — Mark Guards `unfold`, Test at the Transparent-Helper Level

**Lesson**: Adding a new
bounded-greedy `custom` codec in its own §45-isolated module and then TESTING
it from a sibling test module exposes two cross-module-opacity traps that
do NOT appear when the codec is only used in-module.

### Trap 1 — `.roundtrip` / `.dec` / `.wfcv` field calls do NOT discharge cross-module

Calling `(custom_codec ...).roundtrip v r` (or `.dec s`, `.wfcv v`) from a
sibling module fails with Error 19 because the `custom` combinator's
`.roundtrip` lambda (defined in the codec library types module) internally does
`assert (wfcv_custom v); assert (wfcv_prop_custom v); assert (rest_cond_custom v r)`.
Those asserts must unfold YOUR guard functions (`wfcv_custom` = a plain `let`),
and a plain (non-`unfold`) top-level `let` is OPAQUE cross-module (§18) — SMT
cannot reduce `wfcv_custom ""` to `true` from a sibling module.

**Fix**: mark the guard lambdas `unfold` exactly like the encoder:
```fstar
unfold let text_chars0_enc (pred) (s) = seq_of_list (text_string_to_bytes s)
unfold let text_chars0_wfcv (max) (pred) (s) = ...   (* was a plain let — OPAQUE *)
unfold let text_chars0_wfcv_prop (max) (pred) (s) = True
unfold let text_chars0_rest_cond (max) (pred) (s) (r) = ...
```
Without `unfold`, the `.roundtrip` field's internal asserts are unprovable at
the cross-module call site even though the codec's own roundtrip LEMMA
(`lemma_text_chars0_roundtrip`, which calls the guards in-module) verifies fine.

### Trap 2 — test at the TRANSPARENT-HELPER level, not the record fields

Even with `unfold` guards, TESTING the decode result via a bare
`(codec).dec s == Inr (...)´ is fragile: the decoder is a `let rec` scan that
is opaque cross-module (§44/§2).  The established pattern is to test at the
TOP-LEVEL transparent helpers — `text_chars0_dec`, `text_chars0_enc`,
`byte_matchable`, `ascii_ok` — and expose the scan's BASE CASES via explicit
`()`-body unfold lemmas:

```fstar
let lemma_scan0_empty (max) (pred) : Lemma (scan_text_chars0 max pred Seq.empty == []) = ()
let lemma_scan0_nonmatch (max) (pred) (b) : Lemma
  (requires not (byte_matchable pred b))
  (ensures scan_text_chars0 max pred (Seq.create 1 b) == []) = ()
```

The full roundtrip (empty + non-empty) is proven IN the source module by the
`custom` codec's `lemma_*_roundtrip`; the test module should RE-STATE that
source lemma as a concrete vector (a `let ... = lemma_*_empty_roundtrip ...`
binding), NOT re-derive `.dec`/`.roundtrip` cross-module.

### Trap 3 — empty-value encode/decode needs the concrete vector IN the source

`Lemma (ensures text_chars0_enc pred "" == Seq.empty)` and
`Lemma (ensures text_chars0_wfcv max pred "" == true)` do NOT discharge
cross-module: they reduce to `FStar.String.list_of_string "" == []` and
`seq_of_list []` length, which hit the opaque `String`/`Seq` primitives (§11).
Put the concrete empty-roundtrip vector IN the source module (where the scan
and string bridge are transparent):
```fstar
let lemma_text_chars0_empty_roundtrip (max) (pred) : Lemma
  (requires text_chars0_wfcv max pred "" /\ text_chars0_rest_cond max pred "" Seq.empty)
  (ensures text_chars0_dec max pred (text_chars0_enc pred "" ++ Seq.empty) == Inr ("", 0))
  = lemma_text_chars0_roundtrip max pred "" Seq.empty
```
and have the test module `let _x = lemma_text_chars0_empty_roundtrip` (an anchor),
matching the established pattern of re-stating SOURCE lemmas.

### Also: `let ... in` is INVALID in a `Lemma (ensures ...)` clause

A `let attr : xml_attribute = ... in` inside `ensures` is a term-level
construct, not valid in a type/prop position — F* parses it as a syntax error
(Error 168).  Inline the record expression directly (fstar-proofs §30).

### Checklist (new `custom` codec + a sibling test module)

1. Mark the `enc`/`wfcv`/`wfcv_prop`/`rest_cond` guards `unfold`.
2. Prove the full roundtrip `lemma_*_roundtrip` IN the source module.
3. Add a concrete closed vector (`lemma_*_empty_roundtrip`) IN the source module.
4. The test module re-states source lemmas as anchors; it tests only the
   TRANSPARENT helpers + scan base-case unfold lemmas — never `.dec`/`.roundtrip`.
5. No `let ... in` inside `ensures`; inline the value.
6. Re-verify under the full build (`fstar.exe --z3rlimit 80`), not just LSP.

---

## 55. Wiring a (S Attribute)* List into a Fuel-Indexed Recursive Decode

**Verified lesson**: Adding an attribute list
(`[S] [Attribute]` runs, canonical single-space separator) to a recursive
element decoder that is ALREADY proven by §47-path-b bounded computation exposes
TWO traps that LSP-verify but FAIL under the real build `fstar.exe --z3rlimit 80`.

### Trap 1 — the attribute-list fuel must be SEPARATE from the element-depth fuel

If the attribute decoder reuses the SAME `fuel` that indexes element nesting
(`attrs_dec (fuel - 1)`), then a depth-1 element bearing an attribute underflows:
`element_dec 1` → `attrs_dec 0` → the `fuel = 0` base case returns `([], bs)`
WITHOUT consuming the attribute, so the subsequent `/`-vs-`>` dispatch sees the
leading space byte and returns `None`.  The concrete roundtrip lemma
(`<a k="v"/ >`) then fails its decode assert under the full build (LSP does not
catch it — the `assert` is exactly where LSP is looser).

**Fix**: give the attribute list its OWN bound (`let attr_bound : nat = 1024`),
independent of the element depth; `element_dec_body fuel` calls
`attrs_dec attr_bound rest1`, not `attrs_dec (fuel - 1) rest1`.  The two fuels
measure different dimensions (attribute count vs. nesting depth).

### Trap 2 — gate `attrs_dec` behind an `is_ws_byte` head check, or the recursive
unfold breaks the EXISTING no-attribute roundtrip lemmas

Calling `attrs_dec attr_bound` UNCONDITIONALLY (before the `/`-vs-`>` dispatch)
adds SMT weight to EVERY unfold of the recursive `element_dec_body`, enough to
push the previously-green `lemma_element_nested_roundtrip` past the tight rlimit
(§51 Pitfall 1: a dead-for-this-input branch still gets SMT-encoded at each
unfold).  The failure surfaces as an `Assertion failed` on an UNRELATED
`lemma_text_string_to_bytes_roundtrip "hi "` call inside the nested lemma — the
symptom is displaced from the cause.

**Fix**: check `is_ws_byte b` on the byte AFTER the name; only when it is
whitespace do you call `attrs_dec` (and dispatch on its result); otherwise fall
through to the PRE-attribute dispatch path with `attrs = []`, byte-for-byte
identical to the original decoder.  This keeps the no-attribute signal path SMT-
weight-identical, so the existing no-attribute concrete vectors (empty/text/
nested) discharge unchanged.

### Checklist (attribute list + fuel-indexed recursive decode)

1. Attribute count fuel `attr_bound` is a SEPARATE constant from the nesting
   fuel; never `fuel - 1`.
2. Gate `attrs_dec` behind an `is_ws_byte` head check; keep a no-attribute
   fall-through path identical to the pre-change decoder.
3. The canonical separator is a SINGLE space (encode via `ws_unit`'s backward
   map `Some " "`); the decoder still accepts one-or-more whitspace (tab/CR/LF)
   via the shared `ws` codec.
4. Re-verify under the full build `fstar.exe --z3rlimit 80`, not just LSP — both
traps are full-build-only and LSP-green code fails the real build.

## 56. Multi-Byte Node-Prefix Dispatch at the Combinator Layer — Factor the Shared Prefix, Not a New Combinator

**Verified lesson**: A node codec that must
route among element, comment (`<!--`), CDATA (`<![CDATA[`), and PI (`<?`),
all of which share the leading `<`, CANNOT use a bare `alt` chain — `alt`
dispatches on ONE first byte, and the shared `<` collapses all four branches
to the same discriminator.  It also does NOT need a new codec primitive: the
existing prefix-factoring recipe (§52/§53) composes it.

### The recipe

1. Factor the shared `<` ONCE (`then_drop (byte_val 0x3C) …`), then `alt`
   chains on the discriminating byte AFTER `<`:
   - `!` (`0x21`) → comment | CDATA (a second `alt` on `-` (`0x2D`) vs `[` to
     split the `<!` family),
   - `?` (`0x3F`) → PI,
   - name-start → element.
   Each sub-branch's encoder MUST emit [[its]] first byte matching its `alt`
   predicate (`alt_wfcv` checks `Seq.index (c.enc v) 0`), so the leaf codecs
   are built "after `<`" (e.g. `-- content -->`, `[CDATA[ … ]]>`).
2. Split the element codec into a **TAIL** ([from the name]) and the
   `<`-prefixed wrapper — the combinator mirror of the list-level
   [element_dec_body]/[element_dec] split (§47 Option 2).  Otherwise the node
   dispatch, having consumed `<`, has no "element body from name" codec to fall
   through to, and reusing the full (`<`-inclusive) element codec re-introduces
   the double `<`-match.
3. The recursion token is the TAIL, fuel-indexed: `element_tail_codec fuel
   = element_tail (element_tail_codec (fuel-1))`, and
   `element_codec fuel = then_drop < (element_tail_codec fuel)`.  Do NOT
   pass the full (`<`-inclusive) element as the `node_body` parameter — that
   re-creates the cycle the higher-order `self`/`tail` split was meant to break.

### Two full-build-only traps (LSP looser, both Errors)

- **Error 12 (PI target type):** the PI target is a *plain string* in the AST
  (`PI : target:string -> data:string`), so compose `product name_codec …`,
  NOT `product name_record_codec …`.  `name_record_codec : codec name_record`
  (the `{prefix; local}` record); `name_codec : codec string`.  LSP accepts the
  record until the `map_` projection back to `string & string` mismatches.
- **Error 54 (`alt` predicate literal):** `alt`'s predicate is
  `byte -> bool`, and `U8.v b` returns `nat`; write the discriminator as a bare
  nat literal (`fun b -> U8.v b = 0x2D`), NOT `0x2Duy`.  `0xNNuy` is `U8.t`,
  and `nat = U8.t` is a type error.  This is the same nat-literal rule as the
  existing `fun b -> U8.v b <> 0x3C`.

### Checklist (combinator multi-byte-prefix dispatch)

1. Factor the longest common prefix once; the discriminator of EACH `alt` is the
   first byte its sub-encoder actually emits.
2. `alt` predicates use bare nat literals against `U8.v b`.
3. The element branch uses a tail (from-name) codec; the fuel recursion passes
   the tail, not the full element.
4. Verify under the full build `fstar.exe --z3rlimit 80`, not just LSP — both Errors above
   are full-build-only.

## 57. `sum` Is TAGGED (`0x00`/`0x01`); Untagged Single-Byte Choice Requires `alt`, Never `sum`

**Verified lesson**: When building
a character-level codec that must choose between two alternatives on the FIRST
BYTE of content (no room for a tag byte), `sum` is the WRONG combinator and
silently corrupts the wire format.

### The bug

`attr_text_char` (an attribute-value char = literal OR `&`-family) was written:

```fstar
let attr_text_char : codec char =
  map_ ... (sum (bytes [0x26uy;0x71uy;...]) text_char)
```

`sum` is the TAGGED alternation (Combinator 16): its encoder prepends a
`0x00` (Inl) or `0x01` (Inr) discriminator byte, and its decoder reads that
tag first (else `ExpectedSumTag`).  So the encoder emitted a bogus `0x00`
byte before the `&quot;` literal, and the decoder could never parse a real
value whose first byte was neither `0x00` nor `0x01`.

The bug is **self-consistent** — `sum`'s roundtrip field verifies (`dec`
reads the tag `enc` writes) — so it slips through a full build when the codec
is never exercised against a non-empty concrete vector.  Only the empty-value
roundtrip (`greedy_dec_list ... Seq.empty == Inr ([], 0)`, which never calls
`sum_dec`) was stated, so the corruption went unnoticed.

### The fix

Untagged single-byte-prefix choice is `alt` (Combinator 20), which emits only
branch bytes and dispatches on the caller-supplied first-byte predicate:

```fstar
let attr_text_char : codec char =
  map_
    (fun (e: either char char) -> ...)
    (fun c -> if is_attr_literal ... then Some (Inl c) else Some (Inr c))
    (alt attr_literal_char amp_char (fun b -> U8.v b <> 0x26))
```

Reuse the shared `&`-family (`amp_char`) rather than a parallel tagged branch —
its `entity_body` already emits the `&quot;`/`&amp;` literal for the reserved
characters (the §53 prefix-factoring recipe).

### The audit check

Any `codec` whose alternatives dispatch on a CONTENT byte (not one the codec
itself emits) MUST use `alt` (or `one_of` for a non-prefix-disjoint literal
set), never `sum`.  `sum` is only correct when the codec OWNS a tag byte that
is part of its own wire format.  Grep for `sum (` inside character-level
codec builders; if the encoder does not intend a `0x00`/`0x01`
leader, it is a wire-format bug.

### The deeper architectural correction (same review — see §58)

Inline character/entity resolution is a COMBINATOR-layer property (`greedy`
over a per-char codec + `map_` to the value type), NOT a hand-written list-level
scanner.  A parallel list-level "proof mirror" of the combinator surface is a
rule violation and must be DELETED; the combinator's own `.roundtrip` already
proves the roundtrip generically.  See §58 for the full audit and the §18
opacity of a composed codec's `.roundtrip` requires.

## 58. Combinator-Only Parsers — No Hand-Written Parsers, Not Even as §47 "Proof Mirrors"

**Audit finding**: The parsing rule is categorical: ALL parsing and printing
should use the record `codec a` combinators — no standalone `list byte ->
option (t & list byte)` scanners, no `let rec` decoders that mirror a
combinator, period.  A module that hand-rolls a full parser/printer as a
parallel "proof mirror" of the combinator surface is STILL a violation, even
when (a) it is not `include`d in the facade, (b) it is not extracted, and (c)
its only purpose is to state §47 "bounded-computation" roundtrip lemmas.

### The two legitimate uses of a `let rec` scan (NOT violations)

1. **The `.dec`/`.enc` field of a `custom` codec.**  A `custom` codec's decoder
   is a `let rec` scan you pass to `custom` as its `dec` argument; `custom`
   wraps it in the `codec a` record.  `digits_to_int_decode_go`, `one_of_dec`,
   `bytes_decode` in the codec library are the combinator library's own
   internals of this kind.  These are the codec's decoder — not a bypass of the
   codec layer.

2. **A `custom`'s bound lemmas** (`lemma_*_dec_err_bound`/
   `lemma_*_dec_consumed_bound`/`lemma_*_roundtrip`) — they prove the decoder,
   they do not replace a combinator.

### The violation (the shared anti-pattern)

A companion module holds standalone `list byte -> option (t & list byte)`-shaped
functions (`dec_t`, `children_dec`, `attrs_dec`, `node_enc`, `body_enc`,
`scan_name`, `scan_text`, `scan_value`, `scan_ws`, `scan_delim_*`) that are NOT
wrapped in any `codec a`, but MIRROR a combinator surface built from
`greedy`/`text_char`/`alt`/`then_drop`/`one_of`.  This exists only because a §47
"list-level bounded computation" route was used to prove a recursive roundtrip
(undecidable as a naive general lemma) instead of relying on the combinator's
own roundtrip.  The mirrored scanners are the violation; they must be DELETED.

### The correction

Do NOT re-state the §47 concrete vectors by hand-chaining `codec.dec
(codec.enc v)` through `.enc`/`.dec`.  That is §18-blocked (see the RESOLUTION
below); the combinator already proves the roundtrip generically.  The
hand-rolled mirror modules are DELETED; their well-formedness predicates and
concrete/rejection vectors move into the combinator layer or a test module;
delimiter-aware content stays a `codec` (its scan is the `custom` decoder's
internals, use #1 above).

### RESOLUTION — a composed codec's [.roundtrip] is §18-opaque, even in-source

The "correction" above must not be read as "re-state vectors by calling
[c.roundtrip v r] or chaining [.enc]/.dec".  That is WRONG, and the reason is
generic to every combinator-composed codec, not specific to any one package:

- A [map_]/[product]/[alt]/[then_drop]/[between] codec's [.wfcv]/[.wfcv_prop]/
  [.rest_cond] are **§18-opaque [noeq type] record lambdas** (their fields are
  [fun v -> …] expressions, NOT the named functions a [custom] codec stores).
- Therefore [c.roundtrip v r] needs [wfcv v /\ wfcv_prop v /\ rest_cond v r],
  and that [requires] does NOT discharge — in any module, including the one
  that DEFINES the codec.  SMT reports Error 19 at the [codec] type's
  [roundtrip] field, not in your lemma body.
- [unfold]-marking the LEAF guards (the [custom] codec's [wfcv]/[rest_cond]
  arguments, §54 Trap 1) is NECESSARY but NOT SUFFICIENT: it exposes the
  [custom] layer below; it does nothing for the [map_]/[product] lambdas above.
- [c.enc v] / [c.dec s] do NOT [assert_norm] to a literal for a recursive codec,
  even inline, because they bottom out in [let rec] scans inside [custom]
  (the §44 cross-module [let rec] opacity).

**The correct frame (and the three opacity axes, do not conflate them):**

- §15 — [.enc]/.dec fields ARE transparent (they reduce to the stored function).
- §18 — [.wfcv]/.wfcv_prop/.rest_cond/.roundtrip are opaque for COMPOSED codecs
  (they are [map_]/[product] lambdas; only [custom] stores named functions).
- §44 — [let rec] scan/encode bodies are opaque across module boundaries.

**Consequence:** the combinator library ALREADY proves the roundtrip
GENERICALLY — [greedy]'s [roundtrip] is a list induction, and [map_]/[product]/
[alt]/[then_drop]/[between] each COMPOSE sub-roundtrips.  So for a recursive
combinator-built codec there is NO per-value [dec (enc v)] lemma to re-derive
(or any way to).  Concrete test vectors are regression ANCHORS (values the test
module re-states so Integration enforces their presence), NOT re-proven facts.
Do NOT re-derive [dec (enc v)] per-vector — that is re-proving what the
combinator already proves, and it is §18-blocked anyway.

## 59. Variable-Width UTF-8 Scanning at the Seq Level — Extending the §11/§50 Convention Past Single-Byte

**Verified lesson**: The Unicode Name
work needs a UTF-8-aware [codec string] (encode via [char_to_utf8], decode via
[utf8_decode_one]/[mk_char]).  Two facts determine the whole design, both
confirmed by 0-admit probe modules:

### Fact 1 — the byte-fuel misalignment is the silent killer

A multi-char UTF-8 decode indexed by BYTE count does NOT verify.  [char_to_utf8 c]
is 1–4 bytes, so for the head char the fuel step is variable:
[L.length (char_to_utf8 c @ rest) - 1 <> L.length rest] when [c] is multi-byte.
The induction cannot align the byte-fuel recurrence with the char-cons induction
(Error 19 at the roundtrip post-condition).  **Fix: index the scan fuel by CHAR
count, not bytes.**  Return [(chars, remaining-bytes)] so the encoder's
[concatMap char_to_utf8 cs] reconstructs byte-wise:

```fstar
let rec utf8_scan_chars (max: nat) (bs: list byte)
  : Tot (list char & list byte) (decreases max) =
  if max = 0 then ([], bs)
  else match utf8_decode_one bs with
    | None -> ([], bs)
    | Some (c, rest) -> let (cs, rem) = utf8_scan_chars (max - 1) rest in (c :: cs, rem)

let rec lemma_utf8_chars_roundtrip (cs: list char)
  : Lemma (utf8_scan_chars (L.length cs) (L.concatMap char_to_utf8 cs) == (cs, []))
          (decreases cs) = ...
```
The list-level [lemma_utf8_chars_roundtrip] discharges with one IH call plus one
head-char prefix fact — the char fuel aligns with the char induction.

### Fact 2 — the head-char prefix bridge discharges, but ONLY cross-list (not cross-Seq)

The head-char fact is [utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest)].
It VERIFIES cross-module at 0-admit via the same per-byte-case discipline as
[lemma_utf8_roundtrip] (§46): [char_of_u32_of_char c] + [lemma_div_mod code 64]
(and [code/64], [code/4096] for the 3/4-byte cases).  The [@ rest] does NOT block
it — [char_to_utf8 c @ rest] reduces to a cons chain over a finite prefix, and
[utf8_decode_one] pattern-matches the leading bytes, returning [rest] structurally.

BUT the [byte_seq]-level codec CANNOT use [seq_to_list]/[seq_of_list] to reuse
this list proof: [seq_to_list (seq_of_list l ++ r) == l ++ seq_to_list r] was
ORIGINALLY recorded as §11-unprovable, but it is NOT — the codec types module's
`lemma_seq_to_list_of_list_append` proves it 0-admit (see §11 REVISED and §60;
the hand-written `lemma_seq_to_list_append_l` failed only because it did not chain
the transparent internal stdlib bridges).  The codec's [.dec] may now be either
Seq-native OR [seq_to_list]-at-the-boundary.

### The working Seq-native recipe (the §50 delimiter-blocker does NOT apply)

UTF-8 is **prefix-determined**, not delimiter-terminated: the leading byte fixes
the char width [n ∈ {1,2,3,4}].  The §50 blocker is about a SYMBOLIC multi-byte
DELIMITER lookahead; here the leading byte's width is a FINITE per-char prefix, so
[Seq.index (seq_of_list (char_to_utf8 c) ++ rest) k] reduces via [Seq.lemma_index_app1
(seq_of_list (char_to_utf8 c)) rest k] for each [k < L.length (char_to_utf8 c)]:

```fstar
let utf8_char_len (b: byte) : nat = ... (* 1/2/3/4/0 from the leading byte *)
let utf8_seq_decode_one (s: seq byte) : option (char & nat) =
  (* Seq.index s 0 .. n-1; mk_char gates char_of_int at the §46 bound *)
let rec utf8_seq_scan (max: nat) (s: seq byte) (i: nat)
  : Tot (option (list char & nat)) (decreases max) =
  if max = 0 then Some ([], i)
  else if i >= Seq.length s then Some ([], i)
  else match utf8_seq_decode_one (Seq.slice s i (Seq.length s)) with
    | None -> Some ([], i)
    | Some (c, n) -> match utf8_seq_scan (max-1) s (i+n) with ...
```

This extends the [text_chars] convention (fstar-proofs §11/§50, byte-at-a-time
via [Seq.tail]) to variable width: offset-recursion (§52 [hex_decode_go] shape)
+ [Seq.lemma_index_app1] for the continuation bytes, NOT [Seq.tail], NOT
[seq_to_list].  Still Seq-native, still 0-admit, still the [append_assoc]/
[append_slices]/[lemma_seq_of_list_cons] bridge family for the suffix.

### Checklist (first variable-width scan of a package)
1. Fuel = CHAR count (or the decode's consumption unit), never BYTES, when the
   unit is variable-width.
2. Keep the decode Seq-native ([Seq.index]/[Seq.slice] + offset recursion).
   NEVER [seq_to_list (seq_of_list l ++ r)].
3. Bridge continuation-byte lookahead with [Seq.lemma_index_app1 prefix rest k]
   per continuation byte; the prefix [char_to_utf8 c] is a finite [length n]
   prefix so this is the §11-safe form (not the §50 symbolic-delimiter form).
4. Reuse [char_to_utf8]/[utf8_decode_one]/[mk_char]/[lemma_utf8_roundtrip] from
   a UTF-8 codec module; do NOT hand-re-derive the decode (a self-contained
   [char_of_int] without the [mk_char] gate hits the [0xd7ff]/[0xe000] bound, §46).
5. Verify under the full build [fstar.exe --z3rlimit 80], not just LSP — the
3/4-byte branches are where LSP is looser (§47).

> ⚠ **UPDATE — this Sketch was superseded when actually LANDED.**
> The delivered UTF-8 string codec uses the §60 [Seq.seq_to_list]-at-boundary
> form, NOT the offset-recursion + [Seq.lemma_index_app1] Sketch above,
> and lands 0-admit via a SINGLE induction lemma [lemma_utf8_scan_terminate]
> that collapses both [rest_cond] disjuncts.  See §61 for the three full-build
> traps (decreases-max nat-fuel vs begin/end/int, byte-count nat guard).

---

## 60. Delimiter-Aware Content IS a `codec` — `Seq.seq_to_list` at the Boundary Defeats §50

**Verified lesson**: fstar-proofs §50
concluded that delimiter-aware content (comment `-->`, CDATA `]]>`, PI `?>`)
CANNOT be a Seq-level `codec` because the multi-byte lookahead does not reduce
through the opaque `Seq` constructor.  That conclusion is **WRONG for the
`Seq.seq_to_list`-at-the-boundary formulation** — and the fix is simpler than
§50 believed: decode `Seq.seq_to_list` ONCE at the codec boundary, scan at the
LIST level (where the lookahead reduces cleanly), and bridge back with the
in-module `lemma_seq_list_bij_rev` (`seq_to_list (seq_of_list l) == l`), which
is re-exported by the codec library and therefore callable cross-module.

### The three formulations and which one works

1. **`Seq.slice` + lookahead** (§50's first evidence) — FAILS: `slice` of the
   encoder's nested `Seq.append (seq_of_list open) (…)` is opaque.
2. **absolute-offset lookahead (`Seq.index input pos`) without slice** — FAILS:
   `Seq.index (seq_of_list open ++ seq_of_list content ++ seq_of_list close) k`
   does not reduce through the nested `Seq.append` of the ENCODER output.
3. **`Seq.seq_to_list s` at the boundary, then list-level scan** — WORKS
   (0-admit): the decoder does `let bs = Seq.seq_to_list s in scan bs`, the
   roundtrip applies `lemma_seq_list_bij_rev` to bridge `seq_to_list (seq_of_list
   l) == l`, and `assert_norm` on the concrete `scan` closes it.

The key difference: formulation 3 never asks SMT to reduce `Seq.index`/`Seq.slice`
over a STRUCTURED `Seq.append`; it converts the WHOLE input to a list once, at
which point the list-level recursive scan (§50's own proven anchor) operates on a
transparent `list`.  The one bridging fact it needs for the EMPTY suffix
(`seq_to_list (seq_of_list l) == l`) is ALREADY PROVEN in the codec types module
(`lemma_seq_list_bij_rev`); for a GENERAL suffix [s], use
`lemma_seq_to_list_of_list_append l s` (also in the codec types module,
re-exported by the codec library) which proves `seq_to_list (seq_of_list l ++ s) ==
l @ seq_to_list s` — a *callable lemma*, NOT the §11 unprovable Seq fact it was
originally recorded as (§11 REVISED).

### The working recipe (concrete delimiter)

```fstar
(* in a module that opens the codec library — lemma_seq_list_bij_rev is in scope *)
let rec comment_ok (bs: list byte) : Tot bool (decreases bs) =
  match bs with
  | [0x2Duy] -> false | 0x2Duy :: 0x2Duy :: _ -> false
  | _ :: tl -> comment_ok tl | [] -> true

let rec scan_comment (bs: list byte) : Tot (list byte & list byte) (decreases bs) =
  match bs with
  | 0x2Duy :: 0x2Duy :: 0x3Euy :: _ -> ([], bs)
  | b :: tl -> let (c, r) = scan_comment tl in (b :: c, r)
  | [] -> ([], [])

let comment_dec (s: byte_seq) : Tot (decode_result string) =
  let bs = Seq.seq_to_list s in
  let (content, rest) = scan_comment bs in
  (match rest with
   | 0x2Duy :: 0x2Duy :: 0x3Euy :: [] -> Inr (string_of_list content, L.length content)
   | _ -> Inl (mk_decode_error UnexpectedEndOfInput (L.length content)))

let comment_enc (content: list byte) : Tot byte_seq =
  seq_of_list (content @ [0x2Duy;0x2Duy;0x3Euy])

#push-options "--z3rlimit 800 --split_queries always"
let test_single_hyphen () : Lemma
  (ensures comment_dec (comment_enc [0x61uy;0x2Duy;0x62uy]) == Inr ([0x61uy;0x2Duy;0x62uy], 3))
  = lemma_seq_list_bij_rev [0x61uy;0x2Duy;0x62uy;0x2Duy;0x2Duy;0x3Euy];
    assert_norm (scan_comment [0x61uy;0x2Duy;0x62uy;0x2Duy;0x2Duy;0x3Euy]
                  == ([0x61uy;0x2Duy;0x62uy], [0x2Duy;0x2Duy;0x3Euy]));
    ()
#pop-options
```

This proves `<!--a-b-->` (single interior `-`, legal per RFC [15]) roundtrips
0-admit — the exact case §50 claimed was impossible.

### Combinator-only implication (do not conflate)

The finding does NOT license a list-level "proof mirror" (§58).  The correct
deliverable is a codec combinator (`take_until`): the
delimiter-aware scan is the `custom` codec's `.dec` internals (§58 legitimate-use
#1).  Making the combinator GENERIC over a *parametric* `delim: list byte` hits a
2D-induction opacity wall: the content-validity predicate (`no_delim delim bs` =
"no prefix of `bs` is `delim`") and the scan do NOT unfold in lockstep for a
symbolic `delim` — `lemma_scan_until_exact` needs induction over BOTH `content`
and `delim`, and `is_delim_prefix delim (b::tl@delim@r)` cannot be reduced from
`no_delim delim (b::tl)` without a prefix-length argument.  The **per-delimiter
concrete scans** (fixed `-->`/`]]>`/`?>`, the `one_of` per-instantiation pattern)
all verify.  Ship `take_until` as encoder/decoder/wfcv helpers + per-instantiation
roundtrip lemmas (the `one_of` NOTE pattern), NOT a generic `codec` field,
unless/until the 2D induction is cracked.

### Checklist

1. Decode `Seq.seq_to_list` ONCE; scan at list level; never `Seq.index`/`Seq.slice`
   over the encoder's `Seq.append`.
2. Bridge the GENERAL-[r] case with the EXPORTED
   `lemma_seq_to_list_of_list_append l s` — NOT just `lemma_seq_list_bij_rev`
   (which only bridges the empty suffix).
   `lemma_seq_to_list_of_list_append` proves `seq_to_list (seq_of_list l ++ s) ==
   l @ seq_to_list s` for an ARBITRARY `s: byte_seq` (the §60-correction, see §11
   REVISED).
3. Combine the bridge with the list-level [lemma_scan_*_exact content (seq_to_list r)]
   structural induction, plus [List.Tot.append_assoc] + [lemma_is_prefix_self_append]
   + [Seq.lemma_seq_of_list_length] to connect the decoder's [seq_to_list] →
   [is_prefix_of] → scan → string roundtrip chain.
4. Mark the content decoder [unfold] so its [if]/[let]/[match] structure reduces at
   the roundtrip call site (§44 does NOT block a NON-recursive [let]; only the
   [let rec] scan needs the explicit [lemma_scan_*_exact]).
5. Per-delimiter roundtrip lemmas (concrete delims); a GENERIC parametric-[delim]
   roundtrip still hits the 2D-induction wall — but the per-CONCRETE-delimiter
   roundtrip IS general over the CONTENT [list byte] (not just closed vectors).
6. Verify under the full build `fstar.exe --z3rlimit 80`.

---

## 61. Variable-Width UTF-8 String Codec — `seq_to_list`-at-Boundary + `nat`-Fuel Scan

**Verified lesson**: Building the first
variable-width `codec string` (UTF-8 string codec) — encoder =
`concatMap char_to_utf8`, decoder = UTF-8 char run — exercises three
full-build traps that generalise §59 (whose Sketch was de-risked but not
landed) and §60.

### Trap 1 — `decreases` on a `nat` fuel needs a BARE `if fuel = 0`, not a `begin/end` wrapper or `int` fuel

The char scan:

```fstar
(* CORRECT — the `else` branch carries `~(max = 0)`, so `max - 1 : nat` *)
let rec utf8_scan_chars (max: nat) (bs: list byte)
  : Tot (list char & list byte) (decreases max)
  = if max = 0 then ([], bs)
    else match utf8_decode_one bs with
      | None -> ([], bs)
      | Some (c, rest) -> let (cs, rem) = utf8_scan_chars (max - 1) rest in (c :: cs, rem)

(* BROKEN — the `begin ... end` wrapper drops the `~(max = 0)` context AND the
   `else match` no longer feeds `max - 1 >= 0` to the subt-lat-yping query *)
(* `= if max = 0 then ... else begin match ... end` → Error 19 expected nat got int *)
```

Two broken variants both fail with `Error 19 (expected nat got int)` at `max - 1`:
(1) wrapping the `else` in `begin/end`; (2) changing `max` to `int` with
`if max <= 0` — `decreases` requires the measure to be well-founded (`nat`),
and `decreases max` on `max: int` is rejected.  The `digits_to_int_decode_go`
shape (bare `if k = 0 then ... else ... (k-1)`) is the reference form.

### Trap 2 — the decoder's consumed-BYTE count is `int`, needing the §4 guard

A char scan returns `(chars, remaining)`; the codec contract's consumed count is
a BYTE count.  `List.Tot.length bs - List.Tot.length rem` is `nat - nat = int`,
which fails the `decode_result a = either err (a & nat)` subtyping.  Use the
fstar-lang §4 guard:

```fstar
let consumed_bytes =
  if List.Tot.length bs >= List.Tot.length rem
  then List.Tot.length bs - List.Tot.length rem
  else 0 in
```

### The working recipe (general-`r` roundtrip, 0-admit)

1. **Decoder**: `Seq.seq_to_list` ONCE at the boundary, then the list-level
   `utf8_scan_chars max`, then `string_of_list`.  Not offset-recursion (§59's
   Sketch), NOT `Seq.tail`.
2. **The single induction lemma** [lemma_utf8_scan_terminate max cs r'] collapses
   BOTH bounded-greedy [rest_cond] disjuncts into one [requires]:

   ```fstar
   let rec lemma_utf8_scan_terminate (max: nat) (cs: list char) (r': list byte)
     : Lemma (requires max >= L.length cs /\ (L.length cs = max \/ None? (utf8_decode_one r')))
             (ensures utf8_scan_chars max (concatMap char_to_utf8 cs @ r') == (cs, r'))
             (decreases cs)
     = match cs with
       | [] -> ()
       | c :: tl -> lemma_utf8_decode_prefix c (concatMap char_to_utf8 tl @ r');  (* §59 Fact 2 *)
                   lemma_utf8_scan_terminate (max - 1) tl r'; ()
   ```

   The `L.length cs = max` disjunct (bounded) and the `None? (utf8_decode_one r')`
   disjunct (suffix) are DISCHARGED BY THE SAME induction — do NOT write two
   separate lemmas (`lemma_*_bounded` / `lemma_*_prefix`).
3. **Boundary bridge**: [lemma_seq_to_list_of_list_append bytes r] (§60) for the
   general-`r` case; [lemma_utf8_chars_prefix] (the empty-suffix form) is subsumed.
4. **[rest_cond]** shape: `n = max \/ |r| = 0 \/ (|r| > 0 && None? (utf8_decode_one
   (seq_to_list r)))` — the empty-suffix case is subsumed by the third disjunct
   (`utf8_decode_one [] == None`).
5. **Mark the [custom]-codec guards [unfold]** (§54 Trap 1), and prove the
   [custom] bound lemmas with `()` bodies where the guarded subtraction makes
   them definitional.

### Where §59's Sketch was over-complex

§59 recommended a Seq-node offset scan with [Seq.lemma_index_app1] per
continuation byte; the [seq_to_list]-at-boundary form (§60) is simpler AND lands
0-admit for variable-width UTF-8 (which is prefix-DETERMINED, so the §50
delimiter-blocker does not apply).  List-level structural induction over the
char list, bridged by [lemma_seq_to_list_of_list_append], is the whole proof.

## 62. Bracket-Tracking (Depth-Carrying) Content Scan — the `balanced`-MUST-be-`[] -> false` Rule

**Verified lesson**:
A content codec whose terminator is found by TRACKING a BRACKET DEPTH (not a
fixed close-marker lookahead) is provable 0-admit with a `custom` codec, but
ONLY if the well-formedness predicate treats the empty list at the BASE DEPTH
as `false` — never `true`.

### The scan + predicate must be structurally ISO

```fstar
let rec scan_doctype_go (bs: list byte) (depth: nat) : (list byte & list byte) =
  match bs with
  | [] -> ([], [])
  | 0x3Euy :: tl -> if depth = 0 then ([0x3Euy], tl)          (* terminal '>' *)
                    else let (c,r) = scan_doctype_go tl depth in (0x3Euy::c, r)
  | 0x5Buy :: tl -> let (c,r) = scan_doctype_go tl (depth+1) in (0x5Buy::c, r)
  | 0x5Duy :: tl -> if depth = 0 then (...) else let (c,r) = scan_doctype_go tl (depth-1) in (0x5Duy::c, r)
  | b :: tl -> let (c,r) = scan_doctype_go tl depth in (b::c, r)

let rec doctype_balanced (bs: list byte) (d: nat) : bool =
  match bs with
  | [] -> false                       (* NOT d = 0 ! *)
  | 0x5Buy :: tl -> doctype_balanced tl (d+1)
  | 0x5Duy :: tl -> d > 0 && doctype_balanced tl (d-1)
  | 0x3Euy :: tl -> if d = 0 then tl = [] else doctype_balanced tl d
  | _ :: tl -> doctype_balanced tl d
```

### Why `[] -> false` is load-bearing

The roundtrip lemma is the classic structural-induction fact

```fstar
let rec lemma_scan_go_exact (l rest: list byte) (d: nat) : Lemma
  (requires doctype_balanced l d)
  (ensures scan_go (l @ rest) d == (l, rest))
  (decreases l)
  = match l with
    | [] -> ()                       (* requires is FALSE ⇒ vacuous *)
    | 0x5Buy :: tl -> ... lemma_scan_go_exact tl rest (d+1) ...
    | 0x3Euy :: tl -> if d = 0 then assert (tl == []) else ...
```

- **The `[]` base case is the whole trick.**  `scan_go ([] @ rest) d = scan_go rest d`,
  which equals `([], rest)` ONLY when `rest = []`.  With `doctype_balanced [] d == false`,
  the `requires` is unsatisfiable at `l = []`, so the `[]` branch is VACUOUSLY true and
  needs no `rest = []` hypothesis.  With the naive `[] -> d = 0`, the lemma is simply
  FALSE for `l = []` and non-empty `rest` (SMT rightly fails with "could not prove
  post-condition").
- **The induction bottoms out at the terminal `>` (a `0x3E` at depth 0), not at `[]`.**
  `doctype_balanced (0x3E :: tl) 0` forces `tl = []` (the `>` is terminal), so the
  `0x3E`/depth-0 branch is the real base case and does not recurse.

### The general rule

Any depth-carrying scan over delimited content with a single-byte terminal (`>`),
interior single-byte bracket pairs (`[`/`]`), and a "the terminal only counts at
depth 0" rule: write the predicate so the EMPTY list at depth 0 is `false`, and the
induction lemma's `[]` case becomes vacuous.  `assert (ftl == [])` in the terminal
branch gives SMT the `tl = []` fact it needs to close the case.

### Adjacent lesson — UNTAGGED optionality (RESOLVED — see §63)

`optional c` is built on `sum` (§57) and INJECTS a `0x00`/`0x01` tag byte — unusable
for TEXT codecs where "absent" means "no bytes".  And `alt` cannot express an EMPTY
"absent" branch (`alt_wfcv` requires non-empty first-byte-disjoint encodings).  XML
optional fields (`EncodingDecl?`, `SDDecl?`, `XMLDecl?`, `doctypedecl?`) therefore need
a `custom` codec whose `dec` does a list-level prefix test (`is_prefix_of` the fixed
keyword or marker) rather than a combinator.  Same class as the doctype scan above.

> **⚠️ RESOLVED.**  The original draft of §62 treated the STRUCTURED roundtrip as
the §47/§62 SMT wall and fell back to an OPAQUE-string decl.  That diagnosis was
WRONG — the real blocker was the STRING-level well-formedness predicate, not the
scan chain.  The structured (symbolic) roundtrip is provable 0-admit by carrying
the CHAR LIST explicitly (§63).  Untagged optionals are NOT an inherent open
problem; they are a `custom` list-level prefix test whose roundtrip is provable
once the predicates are char-level.

## 63. Structured Parse Round-Trip — Carry the `list char`, Never Match `list_of_string s`

**Verified lesson**: A flat (non-recursive) STRUCTURED codec whose value is a
record with `string` fields (e.g. `decl { decl_version; decl_encoding;
decl_standalone }`) has a **provable general symbolic round-trip** at 0-admit —
the earlier "§47/§62 scan-chain wall" diagnosis was a MISDIAGNOSIS.  The true
blocker is the OPAQUE `FStar.String.list_of_string` primitive, and the fix is to
make the well-formedness predicate and the round-trip lemma both operate on an
EXPLICIT `list char` parameter rather than destructuring `list_of_string s`.

### The failure (string/byte-level predicate)

A predicate that matches `list_of_string s` INTERNALLY cannot be unfolded at a call
site that has SEPARATELY destructured `list_of_string s` — `list_of_string` is an
opaque primitive (§45), so SMT cannot connect the predicate's internal match to the
call-site destructuring, even with `unfold` + `FStar.Math.Lemmas.small_mod` scattered
in the body.

### The fix (char-level predicate over an explicit `list char`)

```fstar
(* version well-formedness over an EXPLICIT char list, not a string *)
let version_chars_ok (cs: list FStar.Char.char) : bool =
  match cs with
  | c1 :: c2 :: dig :: rest ->
    FStar.Char.int_of_char c1 = 0x31 /\ FStar.Char.int_of_char c2 = 0x2E /\
    is_digit_char dig /\ FStar.List.Tot.for_all is_digit_char rest
  | _ -> false

let version_encode_bytes (cs: list FStar.Char.char) : list byte =
  List.Tot.map char_to_byte_trunc cs

let version_decode_bytes (bs: list byte) : option (string & list byte) =
  match bs with
  | 0x31uy :: 0x2Euy :: tl ->
    let (digits, rest) = scan_digit_run tl in
    (match digits with
     | [] -> None
     | _ -> Some (text_bytes_to_string (0x31uy :: 0x2Euy :: digits), rest))
  | _ -> None

(* round-trip over the CHAR LIST directly — DISCHARGES 0-admit *)
let lemma_version_rt (cs: list FStar.Char.char) (rest: list byte) : Lemma
  (requires version_chars_ok cs /\ (match rest with [] -> true | b::_ -> not (is_digit_byte b)))
  (ensures version_decode_bytes (version_encode_bytes cs @ rest)
           == Some (text_bytes_to_string (version_encode_bytes cs), rest))
  (decreases cs)
  = match cs with
    | c1 :: c2 :: dig :: drest ->
      FStar.Math.Lemmas.small_mod (FStar.Char.int_of_char c1) 256;
      FStar.Math.Lemmas.small_mod (FStar.Char.int_of_char c2) 256;
      let digits = List.Tot.map char_to_byte_trunc (dig :: drest) in
      let rec dig_bytes (ds: list FStar.Char.char) : Lemma
        (requires List.Tot.for_all is_digit_char ds)
        (ensures List.Tot.for_all is_digit_byte (List.Tot.map char_to_byte_trunc ds))
        (decreases ds)
        = match ds with
          | [] -> ()
          | x :: tl -> FStar.Math.Lemmas.small_mod (FStar.Char.int_of_char x) 256; dig_bytes tl
      in
      dig_bytes (dig :: drest);
      lemma_scan_digit_run_exact digits rest;
      assert_norm (U8.uint_to_t 0x31 == 0x31uy);
      assert_norm (U8.uint_to_t 0x2E == 0x2Euy);
      assert (0x31uy :: 0x2Euy :: digits == version_encode_bytes cs);
      ()
    | _ -> ()
```

`lemma_scan_digit_run_exact` is the §48/§50 general-tail structural-induction fact:

```fstar
let rec lemma_scan_digit_run_exact (digits rest: list byte) : Lemma
  (requires List.Tot.for_all is_digit_byte digits /\ Cons? digits /\
            (match rest with [] -> true | b::_ -> not (is_digit_byte b)))
  (ensures scan_digit_run (digits @ rest) == (digits, rest))
  (decreases digits)
  = match digits with
    | [d] -> ()
    | d :: tl -> lemma_scan_digit_run_exact tl rest
```

Verified 0-admit: `fstar.exe --no_default_includes --include <ulib> --z3rlimit 800
Sym2.fst` → "All verification conditions discharged successfully" (probe).

### The full codec shape (flat structured value + `custom`)

```fstar
let decl_wfcv (d: decl) : bool =
  version_chars_ok (FStar.String.list_of_string d.decl_version) /\
  (match d.decl_encoding with
   | None -> true
   | Some e -> enc_name_chars_ok (FStar.String.list_of_string e)) /\
  (match d.decl_standalone with None -> true | Some _ -> true)

let decl_dec (s: byte_seq) : decode_result decl =
  let bs = Seq.seq_to_list s in        (* §60/§61: seq_to_list ONCE at the boundary *)
  match decl_scan bs with              (* flat LIST-level scan -> (decl, rest) *)
  | Some (d, rest) -> Inr (d, guarded_length_sub bs rest)
  | None -> Inl (mk_decode_error ExpectedPredicate 0)
```

The untagged optional encoding/standalone clauses are decided by a LIST-level
`is_prefix_of` keyword test inside `decl_scan` (the §62 bracket-scan class), NOT
`sum`/`alt`.  The `string` ↔ `list char` bridge (`list_of_string`/`string_of_list`)
is applied ONCE at the codec boundary via `lemma_text_string_to_bytes_roundtrip`
(already proved 0-admit).  The roundtrip then chains `lemma_scan_digit_run_exact`
(or `lemma_scan_encname_exact`, same shape) + `lemma_text_string_to_bytes_roundtrip`
+ `lemma_seq_to_list_of_list_append` (§60).

### The two genuinely-different shapes (do NOT conflate)

- **Flat record with `string` fields** (`decl`) — the roundtrip IS provable by
  carrying the `list char` explicitly (§63).  The "wall" was string-opacity, not
  undecidability.
- **Mutually-recursive AST** (`xml_element` ⇄ `xml_node`) — the roundtrip is
  GENUINELY §47-undecidable (mutual recursion + second-order `Lemma` params), and
  remains proven via the combinator's generic §43/§58 induction, not bounded
  computation.  This is a DIFFERENT shape; §63 does not apply to it.

### When to apply

Any codec whose value is a flat record with `string` fields whose well-formedness is
"the string matches a small prefix + a char-class run" (version `1.x`, EncName,
entity names, etc.): write the wfcv and the roundtrip over an EXPLICIT `list char`,
never over `list_of_string s`.  Keep the scan at `list byte` (§60) and bridge the two
lists with `List.Tot.map char_to_byte_trunc` + the `small_mod` lemma per char.


## 64. §63's "carry the list char" Does NOT Reach a `string`-Typed Roundtrip — the §45 `string_of_list` Congruence Wall

**Sharpened finding**: §63 states the
STRUCTURED `decl` roundtrip "IS provable by carrying the `list char` explicitly".
That is TRUE for the shape §63 actually VERIFIED — the version-only probe whose
[ensures] compares [dec (enc cs)] to [text_bytes_to_string (version_encode_bytes cs)],
the SAME `text_bytes_to_string` expression (a SELF-referential comparison, no distinct
`string` field).  It is FALSE — or at least NOT reachable by the §63 recipe alone —
for the actual `decl_codec : codec decl` roundtrip, whose [ensures] must
reconstruct a SEPARATE `string` field:

```fstar
(* the target: decl_dec (decl_enc d ++ r) == Inr (d, |enc d|)
   where the DECODER produces d.decl_version = text_bytes_to_string (0x31::0x2E::digits)
   and the INPUT d.decl_version is an arbitrary symbolic string *)
```

To close it you must prove `text_bytes_to_string (0x31 :: 0x2E :: digits) == d.decl_version`,
i.e. substitute the (opaque) `map char_of_int (map char_to_byte_trunc cs) == cs` equality
INTO `string_of_list (…)`.  That is `FStar.String.string_of_list` CONGRUENCE, which does
NOT exist in the F* stdlib.

### The stdlib facts (verified against `FStar.String.fsti`)

`FStar.String.fsti` only exposes (fstar-proofs §45):

```fstar
val list_of_string : string -> Tot (list char)      (* opaque *)
val string_of_list : list char -> Tot string        (* opaque *)
val string_of_list_of_string (s:string) : Lemma (string_of_list (list_of_string s) == s)
val list_of_string_of_list (l:list char) : Lemma (list_of_string (string_of_list l) == l)
```

There is NO `string_of_list`/`list_of_string` congruence — no lemma of the form
`x == y ==> string_of_list x == string_of_list y`.  `lemma_chars_roundtrip_all`
proves `map char_of_int (map char_to_byte_trunc cs) == cs`,
but SMT will NOT substitute that `squash (complex_term == cs)` into `string_of_list
(complex_term)` — the documented §45 `Inr`-payload-congruence limitation.  This is the
REAL wall, NOT scan-chain undecidability (§47) and NOT a missing predicate (§63's
original diagnosis).

### The empirical evidence (three probes)

1. **Version-only §63 recipe** (`version_chars_ok : list char -> bool` +
   `lemma_scan_digit_run_exact`) — VERIFIES 0-admit (the self-referential [ensures]).
2. **The char-level predicates + scan-exact/expect-bytes/bridging lemmas** ported into
   a prolog module — ALL VERIFY 0-admit under the full build `--z3rlimit 80`:
   [`version_chars_ok`]/[`encname_chars_ok`]/[`is_verdigit_char`]/[`is_encname_char`] +
   [`lemma_scan_verdigits_exact`]/[`lemma_scan_encname_exact`]/[`lemma_expect_bytes_exact`]/
   [`lemma_verdigit_chars_to_bytes`]/[`lemma_encname_chars_to_bytes`]/
   [`lemma_verdigit_chars_ascii`]/[`lemma_encname_chars_ascii`].
3. **The string-reconstruction bridge** `text_bytes_to_string (…) == d.decl_version`
   (or `== string_of_list cs`) — FAILS with "Could not prove post-condition", even as a
   `cs`-parameterised `Lemma`; the failure is the §45 substitution, not a resource limit
   (rlimit barely consumed).

### The two clean resolutions (DECISION REQUIRED — architectural)

- **(A) Carry `list char`, not `string`.**  Change `decl.decl_version` /
  `decl_encoding` from `string` to `list char` (or add a `version_chars : list
  char` field), so the roundtrip carries the chars directly and no `string`
  reconstruction is needed.  This is the most-correct spec-conformant form: the
  version/encoding are kept as their grammar's own alphabet.  Touches the AST +
  token/codec modules + downstream consumers of `decl`.
- **(B) Keep the opaque string codec.**  The interim `decl_text_codec : codec string`
  carries the declaration as an opaque validated string, exactly as an opaque
  internal `option string`.  Structurally thinner but fully verified.

### The lesson

§63's "carry the `list char`" fixes the WELL-FORMEDNESS-predicate opacity (matching
`list_of_string s` internally vs. externally).  It does NOT, by itself, make a
`string`-TYPED field's roundtrip provable: the `string` roundtrip additionally needs
`string_of_list` congruence, which stdlib F* does not have.  For any codec whose value
carries a `string` that must be reconstructed and COMPARED (`dec (enc v) == v` for
symbolic `v.string_field`), either (A) carry `list char` in the value type, or (B)
carry the field opaquely (`codec string`).  The two are mutually exclusive for a
single `string`-typed field; do not conflate §63 (predicate opacity) with §45 (string
congruence).

## 65. §64 Decision A (Carry `list char`) Does NOT Reach a General Symbolic Roundtrip Either — the List-Constructor Congruence Wall

**Sharpened finding**:
§64 closed with "either (A) carry `list char`, or (B) carry opaque", implying
(A) would make the structured roundtrip provable.  Empirical probing (isolated
module, zero admits, reusing `lemma_chars_roundtrip_all`) shows (A) is
**necessary but NOT sufficient**: the general symbolic roundtrip still fails with
"Could not prove post-condition", even carrying `list char` and chaining every
supporting fact.

### What verifies 0-admit (all of it)

- char-level predicates `is_verdigit_char`/`is_encname_char`/`version_chars_ok`/
  `encname_chars_ok`;
- the byte-level bridges `verdict_char_to_byte`/`encname_char_to_byte`
  (digit/encname char ⟹ its `char_to_byte_trunc` is a digit/encname byte) and
  their `for_all` lifts (`verdicts_to_bytes`/`encnames_to_bytes`);
- the char→byte→char reconstruction `verdict_chars_to_bytes`/
  `encname_chars_to_bytes` ⇒ `bytes_to_chars (List.map char_to_byte_trunc cs) == cs`;
- the scan-exact lemmas `scan_verdigits_exact`/`scan_encname_exact`/`expect_exact`;
- concrete closed vectors (`scan_verdigits [0x30;0x22] == ([0x30],[0x22])`,
  `bytes_to_chars [0x30] == ['0']`).

### What fails

The **general symbolic** flat-scan roundtrip `scan (enc d) == Some (d, [])`.
Both a `()` body and an explicit chain (`verdicts_to_bytes`, `verdict_chars_to_bytes`,
`scan_verdigits_exact`, `version_chars_bytes_shape`) fail at near-zero rlimit.
The barrier is the SAME §45 substitution limitation, relocated from `string_of_list`
to the **list constructor**: SMT will not substitute the *proven*
`bytes_to_chars (map char_to_byte_trunc cs) == cs` into the scan's reconstructed
`decl_prefix_chars @ bytes_to_chars digits`.  The `== cs` fact is a `squash
(complex_term == cs)`, and `complex_term` is not a bare variable, so SMT does not
rewrite it inside the `::`/`@` construction — exactly `Inr (text_bytes_to_string bs,
n) == Inr (s, n)` (§45), just at the list level.

### The corrected resolution

§64's "two clean resolutions" understate the wall.  The honest 0-admit options are:

- **(B) Opaque carried field — the workable general roundtrip.**  Carry the
  declaration as a validated OPAQUE text token (`custom codec string`, the
  opaque-text-token pattern); the roundtrip is the §45
  `text_bytes_to_string (text_string_to_bytes s) == s` fact.  Expose the
  STRUCTURAL view via a named pure parser (`scan : list byte -> option (t & list
  byte)`) — verified against concrete vectors, NOT a `codec` field.
- **(A') Structured `codec t` + `assume val` roundtrip** (§27) — honest but
  violates the 0-admit requirement; only acceptable if a trade is explicitly
  authorized.

### The general lesson (do not conflate the two walls)

- §45/§63 = WELL-FORMEDNESS-predicate opacity + `string_of_list` congruence.
- §65 = LIST-CONSTRUCTOR congruence: a proven `complex_term == cs` (where
  `complex_term` is not a bare variable) is not substituted into a constructor
  application during roundtrip reconstruction.

For ANY flat structured record codec whose `dec (enc v) == v` must reconstruct a
field by re-scanning its own encoding, the reconstruction hits this barrier UNLESS
the field value is carried opaquely (whole-text) and reconstructed by the opaque
string roundtrip.  Carrying `list char` moves the wall, it does not remove it.

## 66. Untagged-Optional `custom` Codec — Local Transparent `starts_with` Defeats the Cross-Module `is_prefix_of` Opacity Wall

**Verified lesson**: An UNTAGGED-OPTIONAL
field (`decl?` / `doctype?` — absent == zero bytes) cannot use `sum` (§57 tag
byte) nor `alt` (§62 no empty branch), so it is a `custom codec (option a)` whose
`.dec` does a LIST-level prefix test then delegates to an already-proven opaque
leaf codec.  Its `roundtrip_custom` lemma hits TWO distinct walls — and the
naive fixes for them FAIL in a non-obvious way.

### Wall 1 — `is_prefix_of` is opaque cross-module (§18)

`is_prefix_of : list a -> list a -> bool` is a plain `let rec` in the codec
types module, so from any other module SMT treats it as opaque (it does NOT
unfold the recursion).  Consequences:

- A LOCAL `let rec lemma_is_prefix_append p l rest : Lemma (is_prefix_of p l ==>
  is_prefix_of p (l @ rest))` that recurses on `p` does NOT discharge its
  `ensures` — its body's `match p, l` cannot unfold the opaque `is_prefix_of`,
  so the induction is vacuous and the implication is uninterpreted.
- `assert_norm (decl_open_bytes == [0x3C;…])` does not help either: the prefix
  reduces, but `is_prefix_of [0x3C;…] content` still does not unfold against a
  SYMBOLIC `content`.

**Fix**: define a LOCAL transparent prefix scan and reason over IT, not the
cross-module `is_prefix_of`:

```fstar
let rec starts_with (p bs: list byte) : Tot bool (decreases p) =
  match p, bs with
  | [], _ -> true
  | _, [] -> false
  | ph :: pt, bh :: bt -> ph = bh && starts_with pt bt

let rec lemma_starts_with_append (p content rest: list byte) : Lemma
  (ensures starts_with p content ==> starts_with p (content @ rest))
  (decreases p)
  = match p, content with
    | [], _ -> ()
    | _, [] -> ()
    | ph :: pt, ch :: ct -> if ph = ch then lemma_starts_with_append pt ct rest else ()
```

Local `let rec` + local recursive induction lemma (both in the SAME module) is
the same pattern as §43/§48 — the lemma's own `match` unfolds the local `starts_with`.

### Wall 2 — a NON-recursive concrete prefix `match` hits the SMT cons-unfold depth

Writing `starts_with` as a single 9-constructor pattern match (the doctype
`<!DOCTYPE`) rather than a recursion:

```fstar
unfold let doctype_starts_with (bs: list byte) : bool =
  match bs with
  | 0x3C::0x21::0x44::0x4F::0x43::0x54::0x59::0x50::0x45::_ -> true | _ -> false
```

proves `doctype_starts_with content ==> doctype_starts_with (content @ rest)`
for a SYMBOLIC `content` only for the 5-byte decl (`<?xml`) — the 9-byte doctype
FAILS "Could not prove post-condition".  A `match` returning `true` on a symbolic
`content` does NOT give the structural refinement `content = 0x3C::…::tl`, so the
`content @ rest` re-match cannot reduce past SMT's cons-unfold depth (§11's "~12
layers" is optimistic here — the `@` append interaction cuts it shorter).  A
recursive `starts_with` + `lemma_starts_with_append` (Wall 1 fix) handles ARBITRARY
prefix length, because the lemma does the induction instead of SMT's match unfolding.

### The working optional roundtrip shape

```fstar
unfold let optional_decl_dec (s: byte_seq) : decode_result (option string) =
  let bs = Seq.seq_to_list s in
  if starts_with decl_open_bytes bs then
    (match decl_text_dec s with Inr (text, n) -> Inr (Some text, n) | Inl e -> Inl e)
  else Inr (None, 0)

unfold let optional_decl_rest_cond (o: option string) (r: byte_seq) : prop =
  match o with
  | None -> not (starts_with decl_open_bytes (Seq.seq_to_list r))
  | Some text -> decl_text_rest_cond text r

let lemma_optional_decl_roundtrip (o) (r) : Lemma (requires wfcv o /\ rest_cond o r)
  (ensures optional_decl_dec (optional_decl_enc o `Seq.append` r) == Inr (o, Seq.length (optional_decl_enc o)))
  = match o with
    | None -> append_empty_l r; ()
    | Some text ->
      let content = text_string_to_bytes text in
      assert (starts_with decl_open_bytes content);   (* from decl_ok content *)
      lemma_seq_to_list_of_list_append content r;
      lemma_starts_with_append decl_open_bytes content (Seq.seq_to_list r);
      lemma_decl_text_roundtrip text r;               (* the opaque leaf roundtrip *)
      ()
```

Each of `optional_decl_dec`/`optional_decl_enc`/`optional_decl_wfcv`/
`optional_decl_rest_cond` MUST be marked `unfold` (so the `custom` roundtrip
unfolds them), AND the delegated leaf `decl_text_dec`/`decl_text_enc`/
`doctype_dec`/`doctype_enc` MUST be marked `unfold` too (so their `Some text`
reconstruction reduces in the optional's `ensures`).

### Checklist

1. Untagged optional = `custom codec (option a)`; prefix test via a LOCAL
   `let rec starts_with` (NOT the cross-module `is_prefix_of`).
2. Add the LOCAL `lemma_starts_with_append` (recursive induction on the prefix).
3. Mark the optional's `dec`/`enc`/`wfcv`/`rest_cond` and the delegated leaf
   `dec`/`enc` ALL `unfold`.
4. `None` case: `append_empty_l r` + rely on `rest_cond None = not (starts_with …)`.
5. `Some` case: assert the wfcv-conjunct `starts_with prefix content`, bridge
   `lemma_seq_to_list_of_list_append`, then `lemma_starts_with_append`, then the
   leaf's own roundtrip.  Do NOT split `Some`/`None` into a separate helper whose
   `ensures` uses a DIFFERENT term than the outer (`optional_decl_enc (Some text)`
   vs `decl_text_enc text`) — inline the branch so the terms match.
6. Verify under the full build (`fstar.exe --z3rlimit 80`), not just LSP.

## 67. "Opaque Interior" Does Not Mean "Opaque Envelope" — Validate the Structural Shell, Not Just the Delimiter

**Audit lesson**: When a codec carries a
complex token as an OPAQUE `string` (e.g. a doctype/declaration), the "opaque"
decision covers ONLY the piece that is genuinely a separate lift — typically
the INTERIOR (e.g. the subset grammar).  The token's structural ENVELOPE (its
fixed `KEYWORD S Name (S ExternalID)? …'>'` shell: the keyword, the required `S`,
the `Name`, the optional bracketed/quoted sub-tokens) is STILL in scope and must
be validated by a structural predicate, not just a "starts with the open keyword
+ balanced to the close delimiter" check.

### The anti-pattern that slipped through

```fstar
(* WRONG — accepts `<!DOCTYPE>`, `<!DOCTYPE <<<<>>>>` as well-formed *)
let doctype_ok (bs: list byte) : bool =
  starts_with doctype_open_bytes bs && doctype_balanced bs 0   (* only bracket depth *)
```

This validates ONLY (a) the `<!DOCTYPE` prefix and (b) bracket balance to a
terminal `>`.  It never checks the REC [28] production
`'<!DOCTYPE' S Name (S ExternalID)? S? ('[' intSubset ']' S?)? '>'` — the
`Name` is unvalidated, the required `S` is unvalidated, the optional
`ExternalID` is unvalidated.  The stored `doctype : option string` can
be arbitrary balanced garbage and still roundtrip, because the opaque-string
roundtrip (§45) only proves `dec (enc s) == s` — it does NOT reject a `s`
whose bytes are not a doctype.  The module's own header ("doctype is FULLY
structural for Name + ExternalID") was contradicted by the code.

### The correct frame

Split every "carried-opaque" token into ENVELOPE vs INTERIOR:

| Layer | Doctype [28] | In scope? | Enforced by |
|---|---|---|---|
| ENVELOPE | `<!DOCTYPE` keyword | yes | `starts_with` |
| ENVELOPE | `S Name` | yes | a `Name` scan (reuse `name_codec`'s list-level `scan_name`) |
| ENVELOPE | `(S ExternalID)?` | yes | wire the `[75]`/`[11]`/`[12]` codecs in |
| ENVELOPE | `('[' … ']')?` | STRUCTURAL bracket balance only | `doctype_balanced` |
| INTERIOR | `intSubset` markupdecl/DeclSep | NO (separate lift) | opaque, balanced only |

The ENVELOPE predicate is what the roundtrip lemma's `requires` (the codec's
`wfcv`) must include, so a malformed envelope is REJECTED by `.dec`, not just
"accepted and roundtripped opaquely".

### When to apply

Audit any `custom codec string` (doctype, declaration, any "carried opaquely"
token): enumerate its grammar production, and for every non-interior component
(open keyword, required separators, sub-tokens) verify there is a structural
predicate enforcing it AND a rejection lemma proving `.dec == Inl` on a
malformed example.  If a sub-token's codec exists but is referenced nowhere,
that is dead scaffolding and the envelope is silently unenforced.

### Adjacent audit smell — dead codec scaffolding

`external_id_codec`/`system_literal_codec`/`pubid_literal_codec` existed but
were wired into NOTHING (grep finds them only in a docs file).  Dead codec
scaffolding is a red flag: it means either (a) the envelope they were meant to
enforce is silently unenforced, or (b) the code was written for a scope that was
then cut without being deleted.  Each must be wired + proven, or deleted +
documented; never left orphaned.

## 68. A Package Can Be 0-Admit + build-GREEN Yet Have Unproven "Proven" Capacity — Audit the `.Low` Orphans and the Tautological Roundtrip

**Skeptical-review lesson**: A package can
verify 0-admit and extract cleanly while its Low\* layer proves NOTHING about
invertibility.  Two distinct failure modes, both invisible to the full-build
gate:

### (a) Orphaned `.Low` modules — verified+extracted, wired into nothing

`grep` for who `open`s/`include`s each `.Low` module and who binds
its lemmas in the Integration test:

```bash
# Is any module actually USING the Low layer?
for m in $(grep -h '^module' <pkg>/src/*.Low.fst | sed 's/module //'); do
  echo "$m: $(grep -rl "open $m\|include $m" <pkg> --include='*.fst' | grep -v "$m.fst" | wc -l) openers"
done
# Are its LEMMAS bound anywhere?
grep -rn '\.Low\.' <pkg>/test/*Integration.fst | wc -l
```

In a reference package, every `.Low` module has `>= 1` opener, a
`lemma_encode_match`/`lemma_decode_match` bridge into the pure codec, and its
lemmas bound in the Integration test.  A package that ships `.Low` modules with
**zero** openers and **zero** Integration bindings verifies and extracts but
proves-and-composes nothing.  "0-admit, build-GREEN" does NOT mean "the C layer
is correct" — it means "the C layer type-checks".

### (b) The tautological `lemma_roundtrip`

A `.Low` framing module whose `lemma_roundtrip () : Lemma (ensures tag_open ==
0x01 /\ tag_close == 0x02 /\ …)` proves only that the CONSTANT tag bytes are
pairwise distinct — a §26 tautology, not `dec (enc x) == x`.  The canonical
`.Low` roundtrip is inductive over the tag type:

```fstar
(* RIGHT — the canonical shape *)
let lemma_roundtrip (t: token) : Lemma (tag_to_type (tag_of t) == Some t) =
  match t with | Tag_Start -> () | Tag_End -> () | ...

(* WRONG — a constant-value assertion, proves no encode/decode relation *)
let lemma_roundtrip () : Lemma (ensures tag_open == 0x01uy /\ tag_close == 0x02uy) = ()
```

### (c) Dead payload reads in a decode

A decoder bound several fields from a header read then RETURNED only a tag
value — the decoded values were verified against nothing and surfaced nowhere.
A decoder that reads a multi-field header MUST return the fields (or prove they
are irrelevant); reading-and-discarding is dead code that signals an
un-finished framing design (and usually a half-implemented sibling encoder).

### The `wfcv_prop = True` / `rest_cond = True` companion (revisit §24)

The same skeptical pass confirms a key discipline:
`wfcv_prop = True` at a `custom` site is FINE **only** when the non-vacuous
roundtrip lemma's `requires` forces the real `wfcv` gate.  A `= True` field
with NO such roundtrip lemma (i.e. the `custom` is wired to nothing) is the §24
anti-pattern in Low\* clothing.

### When to apply

Before declaring any package DONE, audit its `.Low` modules exactly like a
skeptical reviewer: (1) who opens/includes each; (2) is each lemma bound in
Integration; (3) is each `lemma_roundtrip` a REAL `tag_to_type (tag_of t) ==
Some t` (not a tag-distinctness tautology); (4) does each multi-field decoder
return (not discard) its fields.  A 0-admit build-GREEN package can still fail
all four.

## 69. A Composite Boolean Predicate (`A && not B`) Does NOT `assert_norm` Under Pollution — Decompose and Short-Circuit

**Lesson**: To prove a new gate predicate
`is_target s = is_name_string s && not (is_reserved_target s)` at the lemma
level, DO NOT `assert_norm` the FULL composite:

```fstar
(* WRONG — assert_norm must reduce is_name_string (14-disjunct NameStartChar
   + for_all + list_of_string) AND is_reserved_target AND the not/&&.  Under
   the open'd-module SMTPat pollution (§5) + the full-build `--z3rlimit 80`
   (looser-than-LSP, §47/§52), the full reduction of a MULTI-char string
   fails with Error 19. *)
let lemma_bad () : Lemma (is_target "xml" == false)
  = assert_norm (is_target "xml" == false)
```

**RIGHT — two separable steps:**

1. **REJECT direction short-circuits through the `not`.**  `anything &&
   not true == false`, so `is_target "xml" == false` needs ONLY the
   reducible `is_reserved_target "xml" == true` — the `is_name_string` value
   is irrelevant:

   ```fstar
   let lemma_reject_xml () : Lemma (is_target "xml" == false)
     = assert_norm (is_reserved_target "xml" == true)   (* 3-char string, reduces *)
   ```

2. **ACCEPT direction** needs `is_name_string` to reduce **fully** (head
   NameStartChar + every tail NameChar + `for_all`), which is §5-pollution-
   fragile for multi-char literals.  It reduces cleanly in ISOLATION (a
   minimal probe module) but fails once the open'd codec and text-codec SMTPat
   lemmas pollute the context.  Workarounds, in order:
   - state the accept at the **new predicate** level (`is_reserved_target
     target == false`) rather than the composite `is_target`;
   - for the composite `is_target target == true`, keep the target to a
     SHORT string and `#push-options "--z3rlimit 400 --fuel 4 --ifuel 4
     --split_queries always"`;
   - a longer literal (e.g. `"xml-stylesheet"`) whose `list_of_string`+
     `for_all` reduction exceeds the polluted context should be **dropped** —
     it adds nothing over the reject lemmas + an existing name-accept lemma.

3. The REJECT lemmas (the actual spec-conformance direction) are the ones that
   matter and stay cheap via short-circuiting; the ACCEPT direction is already
   covered by the underlying name codec's accept tests.  Do not let an
   accept-corner lemma's pollution-fragility block the whole change.

### The quote-aware bracket scan is a genuine induction-signature change

Making `balanced_go`/`scan_balanced_go` quote-aware (so `[`/`]`/`>` inside a
quoted literal is inert) means threading a `q: option byte` quote state through
BOTH functions AND their structural-induction lemmas
(`lemma_scan_doctype_go_exact`/`_content_le_len`/`_split_exact`) in lock-step.
Each lemma's `match` must mirror the new `match q with Some qc -> … | None ->
…` branch structure exactly, and every recursive call re-passes the quote state.
The `decreases bs` measure is unchanged (the scan still consumes one byte per
step; the quote state is just an extra carried value).  `is_doctype_quote` must
move BEFORE its first use (definition-before-use — it was previously defined
AFTER `scan_doctype_go`).

## 70. Table-Driven Known-Answer Lemmas — Replace the Lookup Table with the Algorithm

**Verified lesson (fstar-image, CRC-32 and GF(256))**: a codec/hash whose
correctness is pinned by "known-answer" lemmas (`crc32_of_bytes
"123456789" == 0xCBF43926`, `gf_exp (gf_log a) == a`) CANNOT be proven while
the computation is defined over a **256/512-entry opaque lookup table**: SMT
never reduces `List.Tot.nth` over a 256-element list, so `assert_norm` on the
known-answer equality fails and the lemmas end up `admit ()`.  Replacing the
table with the **equivalent algorithmic computation** makes the known-answer
lemma reduce under `assert_norm` and discharges it 0-admit.

### The pattern (CRC-32, verified)

`crc32_update` over a 256-entry reflected table did not reduce.  The
table-free bitwise form does:

```fstar
let crc_step (c: UInt32.t) : UInt32.t =
  if (c &^ uint_to_t 1) = uint_to_t 0
  then c >>^ uint_to_t 1
  else (c >>^ uint_to_t 1) ^^ uint_to_t 0xEDB88320   (* reflected poly *)

let rec crc_byte_fold (c: UInt32.t) (n: nat) : Tot UInt32.t (decreases n) =
  if n = 0 then c else crc_byte_fold (crc_step c) (n - 1)

let crc32_update (crc: UInt32.t) (b: byte) : UInt32.t =
  crc_byte_fold (crc ^^ uint_to_t (U8.v b)) 8

(* then: lemma_crc32_check_value () : Lemma (crc32_of_bytes "...9" == 0xCBF43926)
   = assert_norm (…)  — DISCHARGES *)
```

The `assert_norm` reduces 8 shift-XOR steps per byte (a finite, closed loop),
which the normalizer handles; a 256-entry `List.Tot.nth` does not.

### When it applies

- Any "pre-computed table + known-answer lemma" codec: CRC/Adler (tables),
  GF(256) log/antilog multiplication (tables), base-N lookup tables, AES S-boxes.
- The table is a runtime OPTIMIZATION, not part of the spec; the bitwise/polynomial
  form is the spec, and it is what the proof should carry.  Keep `gf_add`/XOR
  as the algorithmic primitive (`UInt8.logxor` + `FStar.UInt.logxor_*` lemmas).
- The runtime cost is unchanged for GF(256) (8 iterations of shift-XOR == the
  O(1) the table bought) and CRC (8*n bit ops vs n table lookups — acceptable).

### The GF(2^8) field axioms (what Phase 6 needs)

`gf_add = UInt8.logxor` — its laws are FREE via `FStar.UInt`:
`logxor_lemma_1` (identity), `logxor_self` (self-inverse),
`logxor_commutative`, `logxor_associative`.  `gf_mul a b` = shift-XOR mod
0x11D; commutativity/associativity/distributivity/inverse follow by induction
on the 8 multiplier bits + the `logxor` laws.  This replaces the 14 `admit ()`
"field axiom" sites in `Data.Image.QRCode.GF256` with real proofs.

## 71. Non-Linear Arithmetic + Recursive Unfold — the `length (split …)` Wall

**Verified blocker (fstar-image, `Data.Image.PNG.Encode`)**: proving
`length (filter_all_scanlines (split_scanlines data sl)) == height * (sl + 1)`
from `valid_image` (`length data = width * height * bpp`) and `sl = width * bpp`
does NOT discharge, no matter the lemma scaffolding.  SMT must chain THREE
non-linear/unfold facts that it will not combine:

1. `length (take_bytes sl data) = sl` needs `length data >= sl`, i.e.
   `h * sl >= sl` (non-linear; SMT CAN prove this ONE fact in isolation, §13's
   "else gives ~(h=0)" gotcha means you must `assert (h >= 1)` first).
2. `length rest = length data - sl = (h-1) * sl` needs
   `h * sl - sl = (h - 1) * sl`, i.e. `FStar.Math.Lemmas.distributivity_sub_right sl h 1`
   AND multiplication commutativity `sl * (h-1) = (h-1) * sl`.
3. The recursion's TERMINATION: `let (line, rest) = take_bytes sl data` must
   prove `rest << data`, which needs `length line > 0` (`= sl > 0`) plus
   `length line + length rest = length data` chained through the subtraction —
   the SAME non-linear `length data - sl < length data` step.

Even with every `FStar.Math.Lemmas` call and `assert` spelled out, the
`Lemma`'s postcondition (`length (filter_rows h sl data) = length data + h`)
does not discharge — the recursive `filter_rows`/`split_scanlines` self-unfold
across `if`/`match`/`let (row, rest) = take_bytes …` is opaque (§2), and the
length arithmetic is non-linear.  Raising `--z3rlimit` does not help (it is
not under-resourced; near-zero rlimit consumed).

### The honest resolution

- **Do NOT burn a session on this** — it is a known §2 non-linear + §2
  recursive-unfold compound barrier, not a proof gap.
- The types are still fully checked (`requires`/`ensures`); only the SMT query
  is admitted.  Use `--admit_smt_queries true` on the SINGLE function with an
  explicit comment naming the wall (fstar-proofs §34: prefer admit_smt_queries
  over a bare `admit()` body).
- The cleaner alternative (worth it only if the length fact is load-bearing):
  restructure so the length is DEFINITIONAL, e.g. make the filter return a
  `(list byte & nat)` carrying the emitted-filter-byte count, or index the
  recursion on the row count with `take_bytes` returning a length-REFINED pair
  (`(row: list byte{length row = sl}) & list byte`).  Then the row count and
  per-row length are type-carried, not SMT-derived.

### Also relevant (the ascii-codec lossy roundtrip)

A "roundtrip" lemma must match the ACTUAL semantics: `Data.Image`'s ascii codec
thresholds gray pixels (dark `<128` → `0x00`, light `>=128` → `0xFF`), so
`decode_ascii (encode_ascii img) == Some img` is FALSE for e.g. pixel `0x50`.
The correct lemma is a THRESHOLD roundtrip (`map threshold img.data`), not
byte-exact.  Audit the actual forward/back maps before writing `dec (enc v) == v`;
a lossy map silently makes the naive roundtrip unprovable (and false).

---
name: fstar-lowstar
description: F* Low* — KaRaMeL C extraction, buffer patterns, Int.Cast wrappers, C.Loops, warning reference, common extraction errors.
---

# F\* Low\* — C Extraction

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
> Extracted from the full F* skill.  Cross-reference: [fstar index](../SKILL.md).

---

## 1. Architecture: Two-Layer Pattern

- **Spec layer** — GADT or pure types, F\* verification only (NOT extracted to C)
- **Low\* layer** — `inline_for_extraction` functions on `buffer UInt8.t`, extracted to C via KaRaMeL

Spec functions use `Tot`/`GTot`. Low\* functions use `Stack`.

---

## 2. What CAN and CANNOT Extract to C

### CAN Extract
- Primitive types: `int`, `bool`, `byte` (`UInt8.t`)
- Inductive types with data-only constructors (no function fields)
- Structurally recursive functions on `list` (extracts to linked lists)
- `match` on data constructors (extracts to `switch`)
- Stack-allocated buffers (`LowStar.Buffer`)

### CANNOT Extract
- `noeq type` with function fields (closures have no C representation)
- `let rec` through combinators (KaRaMeL can't inline through opaque records)
- Higher-order functions on function-typed lists
- `magic()` — extracts to runtime crash
- Pattern matching on function fields
- Recursive closures (tie-the-knot)
- GADTs with existential type parameters (`#a:Type`) — Warning 26 (Top type)

---

## 3. Buffer Patterns

### Basic Buffer Operations

### Low* Module Conventions

Every Low* module SHALL define module aliases for the standard libraries:

```fstar
open FStar.UInt8
open FStar.UInt32
open FStar.Seq
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LB = LowStar.Buffer
```

Adopting these short module aliases is a common Low\* convention for
uniform, readable code.  Aliases are scoped to the defining
module and do not export to importing modules.

### Basic Buffer Operations

```fstar
open LowStar.Buffer
module B = LowStar.Buffer

let encode_token (v: byte) (buf: B.buffer byte) (off: U32.t)
  : Stack U32.t
    (requires fun h0 -> B.live h0 buf /\ U32.v off + 1 <= B.length buf)
    (ensures fun h0 written h1 ->
      U32.v written == 1 /\
      B.modifies (B.loc_buffer buf) h0 h1)
  = B.upd buf off v; 1ul
```

### `modifies` vs `h0 == h1`

`modifies (loc_buffer buf) h0 h1` allows in-place mutation. Even 0-byte writes (emit nothing) use `modifies`. SMT CANNOT prove `h0 == h1` from `modifies`. For read-only functions, use `h0 == h1` in ensures.

### `modifies` vs `preserves_outside` — existential vs universal framing

`modifies (loc_buffer buf) h0 h1` is **existential** — it says SOME indices
may have changed. For recursive Stack functions, SMT must prove that earlier
writes survive recursive calls. `modifies` alone cannot prove this.

`preserves_outside` is **universal** — it says which indices did NOT change:

```fstar
let preserves_outside (buf: B.buffer byte) (off: U32.t) (n: nat) (h0 h1: HS.mem) : Type0 =
  let s0 = B.as_seq h0 buf in let s1 = B.as_seq h1 buf in
  (forall (i: nat). (i < U32.v off \/ i >= U32.v off + n) /\ i < Seq.length s0 ==>
    Seq.index s1 i == Seq.index s0 i)
```

Both are needed for recursive Stack proofs. `modifies` says what DID change;
`preserves_outside` says what did NOT.

### Buffer slice chaining lemma

When chaining two encode calls, the combined buffer slice must equal
`Seq.append`. SMT needs explicit help:

```fstar
let lemma_slice_append (buf: B.buffer byte) (off n1 n2: U32.t)
  (h_mid h_end: HS.mem) (bs1 bs2: seq byte) : Lemma
  (requires
    slice (as_seq h_mid buf) off (off+n1) == bs1 /\
    slice (as_seq h_end buf) (off+n1) (off+n1+n2) == bs2 /\
    (forall (i: nat). off <= i /\ i < off + n1 ==>
      index (as_seq h_end buf) i == index (as_seq h_mid buf) i))
  (ensures slice (as_seq h_end buf) off (off+n1+n2) == Seq.append bs1 bs2)
```

Body uses `lemma_eq_intro`, `lemma_split`, `slice_slice` from `Seq.Properties`.

### Stack modifies chaining limit (12+ B.upd calls)

SMT cannot chain `modifies` clauses through more than ~12 `B.upd` calls
in a single Stack function.  After ~12 calls, the `modifies` existential
framing saturates and SMT cannot prove `B.live h buf` for subsequent writes.

**Fix**: chunk writes into groups of ≤4 with intermediate `assert`:

```fstar
#push-options "--z3rlimit 120 --split_queries always"
let write_sixteen (buf: B.buffer U8.t) ... : Stack unit ... =
  assert_norm (pow2 32 = 4294967296);
  (* Group 1: 4 writes *)
  B.upd buf 0ul v0; B.upd buf 1ul v1; B.upd buf 2ul v2; B.upd buf 3ul v3;
  let h = HST.get () in assert (B.live h buf);
  (* Group 2: 4 writes *)
  B.upd buf 4ul v4; B.upd buf 5ul v5; B.upd buf 6ul v6; B.upd buf 7ul v7;
  let h = HST.get () in assert (B.live h buf);
  (* Group 3: 4 writes *)
  B.upd buf 8ul v8; B.upd buf 9ul v9; B.upd buf 10ul v10; B.upd buf 11ul v11;
  let h = HST.get () in assert (B.live h buf);
  (* Group 4: 4 writes *)
  B.upd buf 12ul v12; B.upd buf 13ul v13; B.upd buf 14ul v14; B.upd buf 15ul v15
#pop-options
```

Key points:
- `assert_norm (pow2 32 = 4294967296)` for `U32.add` overflow in each group
- `let h = HST.get () in assert (B.live h buf)` between groups resets the
  modifies chain by capturing the current heap
- `--split_queries always` gives each group its own SMT query
- `--z3rlimit 120` is typically enough for up to ~20 writes
- Group size of 4 is safe; 8 can work but is less reliable

### `push_frame` / `pop_frame` — mandatory pairing

`push_frame()` and `pop_frame()` extract to KaRaMeL `KRML_PUSH_FRAME` /
`KRML_POP_FRAME` macros which allocate/deallocate C stack frames.
Every `push_frame()` MUST have a matching `pop_frame()` at the same
lexical level.  Missing `pop_frame()` = C stack frame leak.

**Only use push_frame at foreign/crypto call boundaries.**  For all other
scratch buffer allocation, use `B.sub` with pre-allocated scratch space —
not `push_frame()` / `pop_frame()`.

**Audit check**: every `push_frame()` without a same-function `pop_frame()`
is a BLOCKER bug.  Example bug:

```fstar
(* BEFORE — push_frame leak: the inner helper has its own push/pop,
   so the outer push_frame in the caller never gets popped *)
let outer_helper ... =
  push_frame(); admit();  (* LEAK *)
  inner_helper ... (* this function does push/pop internally *)

(* AFTER — remove unnecessary push_frame; outer_helper just delegates *)
let outer_helper ... =
  admit(); (* composition of the inner helper's sub-call *)
  inner_helper ...
```

**Rule**: if a function only delegates to another function that handles its
own push/pop, the outer function does NOT need push_frame.

### Pure-spec bridge — eliminating recursive Stack

Recursive Stack functions create fresh heap variables per call — SMT cannot
equate these to outer `h1`. Fix: eliminate ALL recursive Stack calls.
Pipeline: `Stack read → lemma bridge → pure spec → convert result`.

```fstar
let decode (c: codec a) (buf: B.buffer byte) (off len: U32.t) =
  let h_init = HST.get () in
  let input_list = read_buffer_to_list_fuel buf off (U32.v len) in
  lemma_read_list_matches_slice_fuel buf off (U32.v len) input_list h_init;
  match c.dec (seq_of_list input_list) with
  | Inr (v, n) -> Inr (v, u32_of_small_nat n)
  | Inl err -> Inl err
```

Zero recursive Stack calls. All recursion in pure `c.dec`.

### `Seq.length` bridge gap

`seq_of_list` has refinement `length l == Seq.length s` but it is NOT
propagated through `let` bindings. Call a bridge lemma after the binding:

```fstar
let s = seq_of_list l in
lemma_seq_of_list_length l;
(* Now SMT knows: Seq.length s == List.Tot.length l *)
```

### `U32.add` overflow bridge

`U32.add` requires `x + y < pow2 32`. `pow2` is opaque to SMT:

```fstar
let lemma_u32_add_no_overflow (x y: U32.t) : Lemma
  (requires U32.v x + U32.v y < 4294967296)
  (ensures U32.v (U32.add x y) == U32.v x + U32.v y)
  = assert_norm (pow2 32 = 4294967296)
```

Use literal `4294967296` instead of `pow2 32` in bounds — SMT can substitute
literals but not `pow2` expressions.

---

## 4. FStar.Int.Cast — Error 56 Fix

`FStar.Int.Cast.uint8_to_uint32` and friends are `Tot`, but their **refined return types** (`{U32.v b = U8.v a}`) cause "bound variable escapes" (Error 56) in `Stack` functions.

**Fix**: `inline_for_extraction let` wrappers with unrefined `Tot` return types:

```fstar
inline_for_extraction
let u8_to_u32 (x: U8.t) : Tot U32.t = FStar.Int.Cast.uint8_to_uint32 x

inline_for_extraction
let u32_to_u8 (x: U32.t) : Tot U8.t = FStar.Int.Cast.uint32_to_uint8 (U32.rem x 256ul)
```

The `inline_for_extraction` + unrefined `Tot` return type drops the postcondition at the wrapper boundary. The helper is inlined at extraction (zero runtime cost). Combine with `#push-options "--admit_smt_queries true"` since the lost refinements prevent SMT from proving overflow-freedom.

### Name resolution with `: Tot U32.t` annotation

When using `inline_for_extraction` with `: Tot U32.t` annotation, the bare
name `uint8_to_uint32` may fail with Error 189 — F* resolves it to the
FUNCTION TYPE (arrow), not the applied expression `uint8_to_uint32 x`.
ALWAYS use the fully qualified name `FStar.Int.Cast.uint8_to_uint32`.

Without the `: Tot U32.t` annotation, the refined return type leaks into
Stack call sites, causing Error 56 (bound variable escapes).  The pattern
is correct but name resolution requires full qualification:

```fstar
(* BROKEN — Error 189: bare name resolves to function type *)
inline_for_extraction
let u8_to_u32 (x: U8.t) : Tot U32.t = uint8_to_uint32 x

(* FIXED — fully qualified name *)
inline_for_extraction
let u8_to_u32 (x: U8.t) : Tot U32.t = FStar.Int.Cast.uint8_to_uint32 x
```

---

## 5. C.Loops Patterns

### `C.Loops.for` — Bounded Iteration

```fstar
open C.Loops

let num_blocks = U32.div total_len 16ul in
C.Loops.for 0ul num_blocks inv_block body_block;
(* Handle remainder separately *)
let rem = U32.rem total_len 16ul in
if U32.gt rem 0ul then ...
```

Prefer `C.Loops.for` over `C.Loops.while` when the iteration count is computable — simpler invariants, no mutable position buffer needed.

### `C.Loops.while` — Correct API

`C.Loops.while` takes a **test** function (`unit -> Stack bool`) and a **body** function (`unit -> Stack unit`). It does NOT take an invariant:

```fstar
val while:
  test: (unit -> Stack bool ...) ->
  body: (unit -> Stack unit ...) ->
  Stack unit ...
```

---

## 6. Extraction Pipeline

```bash
# 1. Verify (REQUIRED before extraction)
fstar.exe --include ./src --cache_checked_modules Module.fst

# 2. Extract to .krml
fstar.exe --include ./src --codegen krml \
  --extract_module Module.Name --odir /tmp/out Module.fst

# 3. Generate C files via KaRaMeL
cp /tmp/out/Module_Name.krml /tmp/out/out.krml
krml -skip-extraction -skip-linking -tmpdir /tmp/out /tmp/out/out.krml

# 4. C files at /tmp/out/Module_Name.c and /tmp/out/Module_Name.h
```

**Key constraint**: F* must verify ALL modules before extraction. Without verification, extraction fails with "Cross-module inlining expects all modules to be checked first."

### Extraction Modes

| Flag | What it extracts |
|---|---|
| `--extract 'krml:*'` | Module + ALL transitive deps |
| `--extract_module A` | Only module A's own definitions |

`--extract_module` does NOT pull transitive dependencies. The resulting `.krml` contains only that module's definitions.

---

## 7. KaRaMeL Warning Reference

| W# | Meaning | Severity |
|----|---------|----------|
| 1 | Not generating code for a provided file | Info |
| 2 | Reference to function without C implementation | Fatal (suppress with `-warn-error -2`) |
| 4 | Type error / malformed input | Fatal |
| 5 | Type application of undefined abbreviation | Fatal |
| 6 | Variable-length array (not supported) | Warning |
| 9 | Need manual static initializers for globals | Warning |
| 11 | Subexpression is not Low* | Warning |
| 15 | Function is not Low* (math ints) | Warning |
| 16 | Arity mismatch (higher-order in C context) | Warning |
| 26 | Expression cast to Top type (GADT existential) | Warning |

**Warning flags**: Use unquoted `-warn-error -9-16` (NOT shell-quoted `-warn-error '-9-16'` — causes KLexer assertion failure).

---

## 8. Extraction Gotchas

### `U32.v` and `U8.v` Have No C Implementation

These are ghost functions. Use pure machine operations or `FStar.Int.Cast` wrappers instead.

### `list @` (append) Has No C Implementation

Use buffers instead of lists in extracted code, or return consumed counts without accumulating values.

### `FStar.Pervasives.either` May Not Be Found

Define custom sum types instead:
```fstar
type decode_result_c = | DR_Inl of error_c | | DR_Inr of U32.t
```

### `inline_for_extraction` on Pure `let` Values

Pure `let` values using `void*` types (e.g., `Lib.IntTypes.uint8`) don't generate proper C symbols. Use concrete types instead:
```fstar
(* CORRECT *)
inline_for_extraction
let state_waiting : FStar.UInt8.t = FStar.UInt8.uint_to_t 0
```

### `Stack` vs `inline_for_extraction`

- `Stack` functions extract directly
- `inline_for_extraction` on `Stack`: works but requires `[@inline_let]` for sub-expressions
- `inline_for_extraction` on `let rec` with GADT: inlines all call sites, eliminating the generic function

### KaRaMeL Checker is Non-Monotonic

Adding more `.krml` files can cause previously-passing functions to fail (new type definitions affect subtype checking).

---

## 9. Buffer Subtyping with `admit()`

`admit()`-based buffer coercions (e.g., casting one buffer type to another) cause KaRaMeL's Low\* re-checker to fail with "subtype mismatch" for functions exceeding ~10 lines.

**Mitigation**: A KaRaMeL patch adding `-skip-lowstar-check 'Module.Name'` bypasses Low\* re-check for specified modules while still generating C code.

---

## 10. C Compilation Flags

```makefile
CFLAGS = -O3 \
  -Wno-implicit-function-declaration \
  -Wno-int-conversion \
  -Wno-incompatible-pointer-types \
  -w \
  -fno-strict-aliasing

# Dead code stripping
CFLAGS  += -ffunction-sections -fdata-sections
LDFLAGS += -Wl,-dead_strip
```

Link against `libkrmllib.a` for `Prims_*` and `FStar_Int_*` runtime symbols.

---

## 11. Monomorphization Naming Mismatches

KaRaMeL may generate different monomorphization suffixes for the same function depending on call context. Use `#define` macros for zero-overhead bridging:

```c
#define GenericModule_reduce GenericModule_reduce_513
```

Or forwarding stubs:
```c
void GenericModule_reduce(uint64_t *a) { GenericModule_reduce_513(a); }
```

---

## 12. KaRaMeL Bundle Syntax

**File-name bundles** (simple):
```
-bundle 'Lib_IntTypes,Lib_Buffer'    # matches .krml filenames
```

**Module-name bundles**:
```
bundle My.Impl.PrimeField=My.Impl.PrimeField.Loop
```
The `=` syntax creates API/implementation bundles controlling monomorphization scope. `+` syntax creates combined API modules.

---

## 13. `.krml` Binary Format

`.krml` files use OCaml's `Marshal` module (binary serialization). NOT a mergeable text format. Each file contains `(version: int, files: (string * decl list) list)`.

---

## 14. F\* Coding Rules for C Extraction

1. **Value bindings must be lowercase**: `tag_open` not `TAG_OPEN`. Uppercase is for type constructors.
2. **`*` is a TUPLE** without `open FStar.Mul`.
3. **No `U32.div`** — use `shift_right` for `/256`, `logand` for `%256`.
4. **Use `U32.t` directly** rather than extracting `nat` then converting back — avoids pow2 opacity.
5. **Error positions are absolute** — never shift them after recursive calls.

## 15. Rust / Wasm backends — non-C-target limitations (VERIFIED 2026-09-27)

The KaRaMeL C backend is production-ready, but the `rust` and `wasm` backends
have hard limitations for real Low\* modules (anything using mathematical
integers or struct-returning functions).  These were root-caused on the
`fstar-codec` `Data.Codec.Low` module.  Do NOT assume the three backends are
interchangeable.

### 15.1 Ghost spec predicates must be pruned (the `FStar.List` reachability)

A Low\* module that `open`s a pure combinator module (a `codec a` record type
full of `list`/`Seq` combinators) does NOT actually leak `FStar.List` into the
generated C — `ensures`/`requires`/`Lemma` spec code is erased.  What DOES leak
is a **top-level `let` value/predicate** used only in `ensures` clauses:

- `let p (…) : prop = …` (a pure predicate returning a proposition) is TRIED
  for extraction and drags `FStar.List.Tot.Base` reachability, breaking rust
  (`FStar.List.Tot.Base.hd … TODO: PDeref`) and wasm
  (`FStar.List.Tot.Base.tail … partially applied`).
- `let f (…) : Pure t … = …` (a pure spec helper consumed only by `ensures` and
  `Lemma` bodies) is likewise extracted, emitting `Prims_list__uint8_t`
  (GC'd list) into C.

**Fix**:
- For a predicate: `noextract` on its own line before `let`:
  ```fstar
  noextract
  let varint_encode_pred (n: nat) (s: Seq.seq U8.t) (i: nat) : prop = …
  ```
- For a spec helper returning a CONCRETE extractable type: change the effect
  `Pure decode_result_c` → `Ghost decode_result_c`:
  ```fstar
  let varint_decode_expected (s: Seq.seq U8.t) … : Ghost decode_result_c … = …
  ```
  (`Ghost` prunes it from the `.krml`; `Pure` does not.)
- `[@ noextract]` / `[@@ noextract]` prefix attributes are a SYNTAX ERROR in
  F* 2025.10.x — use the bare `noextract` keyword on its own line, or `Ghost`.

Verify with: `strings Data_Codec_Low.krml | grep -c varint_encode_pred` → `0`.
The `.krml` binary itself should contain ZERO `FStar.List` references.

### 15.2 wasm backend cannot return structs by value (no multi-value support)

`AstToCFlat.ml` `size_of` maps a wasm value to a SINGLE `I32`/`I64`.  A `LFlat`
(flat struct/tagged-union) return type falls through to
`failwith "size_of: this case should've been eliminated"`.  `decode_result_c`
(a `DR_Inl of {code;pos} | DR_Inr of {n;value}` variant, 20 bytes / 2 fields)
is therefore UNRETURNABLE from a wasm-exported function.

- `-fnostruct-passing` and `-by-ref T` do NOT fix it: the `[AstToC♭]` lowering
  still calls `size_of` on the return type.
- `-d cflat` shows `Data_Codec_Low_decode_result_c (size=20, 2 fields)` then the
  `size_of` failure — the struct layout is computed fine; only the single-
  value RETURN size is impossible.
- Functions returning machine ints (`encode_* → U32.t`) are wasm-fine; functions
  returning a sum/record (`decode_* → decode_result_c`) are not.
- The fix is an API refactor to out-parameters (return `U32.t` status, write
  `n`/`value`/`code`/`pos` via pointer args) — the classic C ABI pattern.  This
  is a big change to the 0-admit module, gated behind OpenSpec (Mandate 15).

The template's `wasm` derivation `works` because `Example.fst` returns only
machine ints — do NOT cargo-cult it onto a struct-returning Low\* module.

### 15.3 rust backend — `krml_checked_int_t` empty type + no runtime crate

`PrintMiniRust.ml:172` maps `Constant.CInt` (the mathematical-int
`krml_checked_int_t`) to `""` (empty string), so any body using `U32.v`/`U8.v`/
`%`/`/` emits Rust like `let b4_val:  = crate::prims::op_Modulus(…)` (blank type
annotation) and `rustc` fails.

Additionally, `-minimal -bundle Mod=\*` emits `crate::fstar::uint8::uint_to_t`,
`crate::prims::op_Division`, `crate::lowstar::ignore::ignore` references, but
KaRaMeL ships NO standalone Rust runtime crate for `fstar`/`prims`/`lowstar`
(unlike the C `libkrmllib.a`).  The KaRaMeL rust-val test harness `sed`-injects
`mod lowstar { pub mod ignore { … } }` by hand — proof there is no shipped
runtime.

- Rust extraction only `works` for modules with NO mathematical int ops (the
  template's bare `add`/`xor`), exactly as C-target `Warning 15` flags
  "uses mathematical integers".
- Fixing needs a KaRaMeL patch (`Constant.CInt -> "i64"`) PLUS hand-written
  `fstar`/`prims`/`lowstar` runtime shims — toolchain work, not source surgery.

### 15.4 Minimal runtime `.krml` set (do NOT glob all 3515)

Pass ONLY the runtime `.krml` the module reaches, not
`${fstar-krml}/krml/*.krml` (thousands of files incl. `FStar_List_Tot_Base`,
which forces the list reachability).  For `Data.Codec.Low` the set is:

```
FStar_UInt FStar_Int FStar_UInt8 FStar_UInt16 FStar_UInt32
FStar_Seq_Base FStar_Int_Cast FStar_Pervasives LowStar_Buffer
FStar_HyperStack FStar_HyperStack_ST
FStar_Monotonic_Heap FStar_Monotonic_HyperHeap FStar_Monotonic_HyperStack
```

(discoverable via `grep -oE 'FStar_[A-Za-z0-9_]+|Prims_[A-Za-z0-9_]+' *.c | sort -u`
on the generated C).  Add `-add-include '"krml/internal/compat.h"'` for the
Warning 15 math ints and link `${karamel.home}/krmllib/dist/generic/libkrmllib.a`
to resolve `Prims_op_Division` etc.

### 15.5 `-drop` takes ONE comma-separated name (not space-joined)

`-drop A B C` mis-parse → `Unknown file extension for B`.  Use
`-drop A,B,C` or one `-drop` per name.  Note `-drop` drops MODULES, not
functions — it cannot remove a single struct-returning function.

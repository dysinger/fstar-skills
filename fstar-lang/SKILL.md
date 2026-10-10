---
name: fstar-lang
description: F* core language — types, effects, operators, syntax, modules, typeclasses, tuples, termination, keyword table.
---

# F\* Core Language

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
> Extracted from the full F* skill.  Cross-reference: [fstar index](../SKILL.md).

---

## 1. Core Types (from Prims.fst)

| Type | Definition | Notes |
|---|---|---|
| `bool` | `assume new type bool : eqtype` | `true`, `false` |
| `int` | `assume new type int : eqtype` | Mathematical integers |
| `string` | `assume new type string : eqtype` | Primitive strings |
| `unit` | `assume new type unit : eqtype` | `()` is the sole inhabitant |
| `nat` | `i: int{i >= 0}` | Non-negative integers |
| `pos` | `i: int{i > 0}` | Positive integers |
| `nonzero` | `i: int{i <> 0}` | Non-zero integers |
| `list a` | `Nil \| Cons hd tl` | Polymorphic linked list |
| `option a` | `None \| Some v` | Optional value |
| `either a b` | `Inl v \| Inr v` | Sum type |
| `tuple2 a b` to `tuple14` | | Tuples up to arity 14 |
| `exn` | `assume new type exn : Type0` | Extensible exception type |
| `squash p` | `x: unit{p}` | Proof-irrelevant proposition |

### Logical Connectives

| Syntax | Definition |
|---|---|
| `True` | `squash trivial` |
| `False` | `squash empty` |
| `a == b` | `squash (equals a b)` |
| `p /\ q` | `squash (pair p q)` |
| `p \/ q` | `squash (sum p q)` |
| `p ==> q` | `squash (p -> GTot q)` |
| `p <==> q` | `(p ==> q) /\ (q ==> p)` |
| `~p` | `p ==> False` |
| `forall x. p x` | `squash (x:a -> GTot (p x))` |
| `exists x. p x` | `squash (x:a & p x)` |

---

## 2. Module System

### `open` vs `include`

| Mechanism | Syntax | Transitive? |
|---|---|---|
| `open M` | Makes M's symbols available in current module only | No |
| `include M` | Copy-pastes M's content; downstream sees symbols | Yes |

- `open` adds to `scope_mods` (per-module, ephemeral). Not tracked in `env.includes`.
- `include` adds to `scope_mods` AND `env.includes` AND unions `trans_exported_id_set`.
- Downstream consumers of a re-exporter DO NOT see symbols from modules it merely `open`s.

**Rule**: Use `include` for re-exporters. Use `open` for internal use.

### `.fsti` / `.fst` Interface Files

F* supports splitting a module into interface (`.fsti`) and implementation (`.fst`).

**What can go in `.fsti`**: `type` definitions (including GADTs), `val` declarations, pure `let` definitions, `unfold let`, `assume`, `open`, module aliases.

**What CANNOT**: Effectful `let` definitions (Stack, STATE), `let rec ... and ...` implementations.

**Why use `.fsti`**:
- Forward declarations: `val` in `.fsti` makes a function available anywhere in `.fst`
- Public API boundary: only `.fsti`-declared symbols are visible downstream
- Separate compilation: `.fsti` can be verified independently

**Reliability caveats**:
- Automatic discovery unreliable — pass both files explicitly
- Error 47 (duplicate names) when both `.fsti` and `.fst` passed
- Cached `.checked` interference from pre-`.fsti` builds
- Must be git-tracked for nix flakes
- Public symbol explosion: all ~60+ downstream symbols need `val` declarations
- **`val` in `.fst` files DOES NOT always work for forward declarations** —
  a `val` before a `#push-options` block may not resolve inside it.
  F* requires definition-before-use for `let`-bound functions called from
  within `#push-options` blocks.  Move the definition before the call site;
  do not rely on `val` for forward-declaring functions called inside
  `#push-options` or `#pop-options` regions.

### Module Alias Shadowing

When both `LowStar.Buffer` and `LowStar.Monotonic.Buffer` are opened, the second shadows names from the first. Module aliases (`module LB = LowStar.Buffer`) may resolve to the wrong module due to `open` taking precedence in name resolution. Use fully qualified names when ambiguous.

### Module Aliases Are Not Re-Exported via `open`

When module A does `module L = FStar.List.Tot` and module B does `open A`,
the alias `L` is NOT available in module B.  Only type/function symbols are
brought into scope; module aliases stay in their defining module.

```fstar
(* A.fst *)
module A
module L = FStar.List.Tot
let f x = L.length x  (* OK — L is in scope *)

(* B.fst *)
module B
open A
let g x = L.length x  (* Error 72 — L is not in scope *)
let g x = FStar.List.Tot.length x  (* OK — use the full path *)
```

**Fix**: importing modules must define their own module aliases even when
they `open` a module that already defines them.  This differs from OCaml
where `open M` brings module aliases into scope.

---

## 3. Effect System

### Effect Hierarchy

```
PURE → Tot → DIV → EXN → ALL → ML
PURE → Tot → GHOST → GTot → STATE
```

### Common Abbreviations

| Effect | Definition | Use |
|---|---|---|
| `Tot a` | Total pure computation | All pure functions |
| `GTot a` | Total ghost computation | Spec functions, erased |
| `Pure a pre post` | Hoare-style PURE | Requires/ensures |
| `Ghost a pre post` | Hoare-style GHOST | Requires/ensures, erased |
| `Lemma pre post` | `Pure unit pre (fun r -> post)` | Squashed proof |
| `Stack a pre post` | Low* stateful | C-extractable |

### Lemma Syntax

```fstar
Lemma (ensures post)
Lemma (ensures post) [SMTPat ...]
Lemma (ensures post) (decreases d)
Lemma (requires pre) (ensures post)
Lemma (requires pre) (ensures post) [SMTPat ...]
Lemma (requires pre) (ensures post) (decreases d)
```

### Effect Compatibility

- `Tot <: GTot` — can call Tot from GTot
- `Tot <: Stack` — can call Tot from Stack
- `GTot` is NOT a sub-effect of `Stack` — cannot call GTot from Stack (Error 53)
- `Stack` is NOT a sub-effect of `GTot` — cannot call Stack from Lemma

---

## 4. Numeric Operators

**`a * b` creates a TUPLE TYPE, not multiplication.** Use `Prims.op_Multiply a b` or open `FStar.Mul`.

| Operator | Prims Name | Concrete Syntax |
|---|---|---|
| `+` | `op_Addition` | `a + b` |
| `-` | `op_Subtraction` | `a - b` |
| `-` (unary) | `op_Minus` | `-a` |
| `/` | `op_Division` | `a / b` (b nonzero) |
| `%` | `op_Modulus` | `a % b` (b nonzero) |
| `<=` | `op_LessThanOrEqual` | `a <= b` |
| `<` | `op_LessThan` | `a < b` |
| `>=` | `op_GreaterThanOrEqual` | `a >= b` |
| `>` | `op_GreaterThan` | `a > b` |
| `=` | `op_Equality` | `a = b` (eqtype) |
| `<>` | `op_disEquality` | `a <> b` (eqtype) |
| `*` | `op_Multiply` | tuple by default; multiply if `FStar.Mul` open |

### `nat - nat` Returns `int`

`nat - nat` returns `int` (via `Prims.op_Subtraction`), not `nat`. Use `if a >= b then a - b else 0` to keep the result in `nat`:

```fstar
let remaining = if U32.v len >= consumed then U32.v len - consumed else 0 in
(* remaining is nat because both branches return nat *)
```

### Integer literal suffixes — `ul` (UInt32) vs `uL` (UInt64), case matters

F* fixed-width integer literals disambiguate by the case of the suffix letter:

| Suffix | Type | Width |
|---|---|---|
| `uy` | `FStar.UInt8` | 8 |
| `us` | `FStar.UInt16` | 16 |
| `ul` (lowercase L) | `FStar.UInt32` | 32 |
| `uL` (uppercase L) | `FStar.UInt64` | 64 |
| `uL` / `UL` | `FStar.UInt64` | 64 |

**`0x…uL` (capital L) is `UInt64.t`, `0x…ul` (lowercase) is `UInt32.t`.**  A 256-entry
`list UInt32.t` written with `uL` fails **"Error 54: UInt64.t is not a subtype of
the expected type t"** (i.e. `UInt32.t`) — the fix is a global `uL` → `ul` in the
table literals.  This bit the CRC-32 table in fstar-image (2026-10-10): the
"published constants" embedded as `0xEDB88320uL` were UInt64, silently the wrong
width until the `list UInt32.t` annotation forced the error.  Named constants
(`uint_to_t 0xEDB88320` with `open FStar.UInt32`) avoid the suffix entirely and
are preferred for single values; a LITERAL TABLE needs the `ul` suffix on every
entry.

---

## 5. Typeclass System

### `class`/`instance` (Tactical)

```fstar
open FStar.Tactics.Typeclasses

class deq a = {
  eq : a -> a -> bool;
  eq_dec : squash (forall x y. eq x y <==> x == y);
}

instance int_deq : deq int = {
  eq = (fun x y -> x = y);
  eq_dec = ();
}
```

Usage: `{| deq a |}` for implicit dictionary passing.

### `noeq type` (Manual Dictionary Passing)

```fstar
noeq type functor (f: Type -> Type) = {
  fmap: #a:Type -> #b:Type -> (a -> b) -> f a -> f b;
}

val functor_list: functor list
let functor_list = {
  fmap = (fun #a #b (g: a -> b) (xs: list a) ->
    match xs with
    | [] -> []
    | x :: ys -> g x :: functor_list.fmap g ys);
}
```

**Always use `noeq`** for records with function fields — F* cannot prove decidable equality.

### Syntax Rules

- `{| constraint |}` — implicit dictionary (BRACES + PIPES + SPACES)
- `#a:Type` — implicit type parameter (compiler infers)
- `a:Type` — explicit type parameter (caller provides)

---

## 6. Concrete Syntax (Desugaring)

| Concrete Syntax | Desugars To |
|---|---|
| `a & b` | `tuple2 a b` |
| `a & b & c` | `tuple3 a b c` |
| `(a, b)` | `Mktuple2 a b` |
| `x:a & b x` | `dtuple2 a b` |
| `(\| x, y \|)` | `Mkdtuple2 x y` |
| `a -> Tot b` | Total arrow |
| `a -> GTot b` | Ghost total arrow |
| `SMTPat p` | `smt_pat p` |
| `SMTPatOr ps` | `smt_pat_or ps` |
| `assert p` | `_assert p` |
| `assume p` | `_assume p` |
| `admit ()` | Escape hatch |
| `magic ()` | Escape hatch |

---

## 7. Inductive Type Syntax

**Use `->` between fields, NOT `*`:**

```fstar
(* CORRECT *)
type expr =
  | Literal: pv:primitive -> expr
  | Variable: name:string -> expr
  | BinOp: left:expr -> op:string -> right:expr -> expr

(* WRONG — tuple syntax *)
type expr = | Add of expr * expr
```

### `noeq` for Function Fields

```fstar
(* REJECTED — F* cannot prove decidable equality *)
type my_class (f: Type -> Type) = {
  method: #a:Type -> f a -> int;
}

(* ACCEPTED *)
noeq type my_class (f: Type -> Type) = {
  method: #a:Type -> f a -> int;
}
```

### GADT Strict Positivity

F* enforces strict positivity: a constructor cannot have a function argument whose return type mentions the type being defined. This prevents `Fix`-style self-referential constructors. Workaround: recursive FUNCTIONS (not values), or the `Custom` constructor pattern.

---

## 8. Termination and `decreases`

### Syntax

```fstar
let rec f (x: t) : Tot result (decreases x) = ...

(* Lexicographic *)
let rec g (x: t1) (y: t2) : Tot result (decreases %[x; y]) = ...

(* Well-founded *)
let rec h (...) : Tot result (decreases {:well-founded ord} x) = ...
```

`decreases` goes INSIDE the return type, after `Tot`:

```fstar
(* CORRECT *)
let rec fold_right (f: a -> b -> b) (xs: list a) (acc: b) : Tot b (decreases xs) = ...

(* WRONG *)
let rec fold_right ... (decreases xs) : Tot b = ...
```

### Fuel Pattern — Use `int` Not `nat`

```fstar
let decode_loop (input: cursor) : Tot result =
  let rec loop (fuel: int) (cur: cursor) : Tot result (decreases fuel) =
    if fuel <= 0 then base_case
    else ... loop (fuel - 1) (advance cur) ...
  in
  loop initial_fuel initial_state
```

Use `int` for fuel (not `nat`) to avoid `nat - 1` returning `int`.

### Mutual Recursion Requires `decreases` on All

```fstar
let rec f (x: a) : Tot b (decreases x) = ...
and g (y: c) : Tot d (decreases y) = ...
and h (z: e) : Tot f (decreases z) = ...
```

---

## 9. Tuple/Pair Operations

```fstar
let fst (x: tuple2 'a 'b) : 'a = Mktuple2?._1 x
let snd (x: tuple2 'a 'b) : 'b = Mktuple2?._2 x

(* Dependent pair *)
let dfst (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot a = Mkdtuple2?._1 t
let dsnd (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b) : Tot (b (Mkdtuple2?._1 t)) = Mkdtuple2?._2 t
```

---

## 10. Escape Hatches

```fstar
assume val _assume (p: Type) : Pure unit True (ensures fun x -> p)
assume val admit   : #a: Type -> unit -> Admit a
assume val magic   : #a: Type -> unit -> Tot a

let unsafe_coerce (#a #b: Type) (x: a) : b = admit (); x
```

---

## 11. Keyword Collision Table

| Haskell/Common | F* Safe Name | Notes |
|---|---|---|
| `and` | `and_` | Boolean conjunction |
| `or` | `or_` | Boolean disjunction |
| `not` | `not_` | Boolean negation |
| `all` | `all_` | List.for_all |
| `any` | `any_` | List.existsb |
| `some` | `some_` | Alternative.some |
| `many` | `many_` | Alternative.many |
| `fail` | `fail_` | Alternative.fail |
| `try` | `try_` | Attempt/backtrack |
| `eof` | `eof_` | End of input |
| `total` | `total_` | Causes Syntax Error 168 |
| `type`, `match`, `let`, `in`, `if`, `then`, `else`, `fun`, `function` | Reserved | Cannot use |
| `module`, `open`, `val`, `rec`, `class`, `instance`, `effect`, `of`, `as` | Reserved | Cannot use |

### Effect Name Collisions with GADT Constructors

Avoid naming GADT constructors `Pure`, `Lemma`, `Ghost`, `Stack`, `Tot`, `GTot`, `Dv`, `St`, `Ex`, `ML`, `ALL` — these shadow effect names. If unavoidable, use fully qualified `Prims.Pure` to disambiguate.

---

## 12. Norm Steps

```fstar
noeq type norm_step =
  | Simpl | Weak | HNF | Primops | Delta | Zeta | ZetaFull
  | Iota | NBE | Reify
  | UnfoldOnly : list string -> norm_step
  | UnfoldOnce : list string -> norm_step
  | UnfoldFully : list string -> norm_step
  | UnfoldAttr : list string -> norm_step
```

### Usage

```fstar
let result = norm [delta; iota; zeta] some_expression
assert_norm (1 + 1 == 2)
reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic
```

`assert_norm (pow2 32 = 4294967296)` computes at type-checking time and adds the equality to SMT context. However, SMT **cannot substitute** this equality into goals — only into asserted facts. Structure goals to use the literal directly when possible.

### `assert_norm` checks definitional equality, not extensional

`assert_norm (f == g)` only succeeds if `f` and `g` are **definitionally**
equal (identical after unfolding all definitions).  If `f` expands to
`h1 o rem` and `g` expands to `h1` (without `rem`), the assert fails
even though the functions are extensionally equal for the relevant inputs.

**Fix**: `assert` + explicit reasoning about the specific values:
```fstar
(* WRONG — definitional equality fails across the rem wrapper *)
let lemma_cast_value (x: U32.t {U32.v x < 256})
  : Lemma (U8.v (u32_to_u8 x) == U32.v x)
  = assert_norm (u32_to_u8 == FStar.Int.Cast.uint32_to_uint8)  // FAILS

(* RIGHT — assert the value-level equality, let SMT use refinements *)
let lemma_cast_value (x: U32.t {U32.v x < 256})
  : Lemma (U8.v (u32_to_u8 x) == U32.v x)
  = assert_norm (pow2 32 = 4294967296);
    assert (U32.rem x 256ul == x);  // true because x < 256
    ()  // SMT chains: definitional expansion + rem-identity + Int.Cast refinement
```

---

## 13. Naming Convention

| Category | Convention | Examples |
|---|---|---|
| Functions/values | snake_case | `fold_left`, `fmap` |
| Type aliases | snake_case | `type my_type = ...` |
| Typeclass names | snake_case | `functor`, `applicative` |
| Class methods | snake_case | `fmap`, `traverse` |
| Data constructors | PascalCase | `Some`, `None`, `Left`, `Right` |
| Module names | PascalCase.Dot.Notation | `Data.Functor`, `Control.Monad` |
| Operator definitions | spaced operators | `let ( >>= ) = ...` **SPACES REQUIRED** |

---

## 14. F\* vs Haskell Quick Reference

| Haskell | F* |
|---|---|
| `class Functor f` | `noeq type functor (f: Type -> Type)` |
| `instance Functor []` | `val functor_list: functor list` + `let functor_list = {...}` |
| `Either a b` | `either a b` (`Inl`/`Inr`) |
| `Maybe a` | `option a` (`None`/`Some`) |
| `(a, b)` | `(a, b)` is `tuple2 a b` |
| `a -> b` | `a -> Tot b` (total) or `a -> ML b` (effectful) |
| `Int` | `int` |
| `Integer` | `int` (unbounded) |
| `String` | `string` |
| `Bool` | `bool` |
| `[a]` | `list a` |
| `:t` type annotation | `(x : t)` |

---

## 15. Gotchas

### `else` of `if i < n` gives `~(i < n)`, NOT `i >= n`

F* puts `~(i < n)` in the SMT context for the `else` branch, not `i >= n`.
Rewrite with the positive condition:

```fstar
(* WRONG — SMT has ~(i < n), not i >= n *)
if i < n then ... else lemma_requires_i_ge_n i n

(* RIGHT — positive condition *)
if i >= n then lemma_requires_i_ge_n i n else ...
```

### `U32.sub` precondition in `else` of `U32.lt` — use `U32.lte` + `assert`

`U32.sub current ticket` requires `U32.v ticket <= U32.v current`.
After `if U32.lt current ticket then ... else`, the `else` branch gets
`~(U32.v current < U32.v ticket)` — SMT cannot derive `U32.v ticket <= U32.v current`.

**Fix**: `let`-bind the `U32.lte` result and use explicit `assert` with `--split_queries always`:

```fstar
let time_ok = U32.lte ticket_time current_time in
if time_ok then (
    assert (U32.v ticket_time <= U32.v current_time);
    let age = U32.sub current_time ticket_time in
    ...
) else ...
```

The `let`-binding makes the condition a named SMT term.  `assert` forces
SMT to discharge it in its own query.  Used with `--split_queries always`.

### `*` without `open FStar.Mul` is a tuple type operator

By default, `a * b` is a tuple type. For multiplication, `open FStar.Mul`.
Without it, `acc * 10` produces Error 189: "Expected expression of Type got nat."

**Cache-masked bug**: `open FStar.Mul` from an imported module is NOT transitive.
However, `--cache_checked_modules` loads transitive `.checked` files which carry
`FStar.Mul` in their environment, masking the missing import.  A from-source
LSP check always catches this.  Every module using `*` for multiplication
MUST have its own `open FStar.Mul`.  See fstar-proofs §35.

### `decreases` must be on the SAME LINE as the return type

For functions with 3+ curried parameters:

```fstar
(* CORRECT *)
let rec f (a: nat) (b: nat) (n: nat) : Tot nat (decreases n) = ...

(* WRONG — separate line causes Error 189 *)
let rec f (a: nat) (b: nat) (n: nat)
  : Tot nat (decreases n) = ...
```

### Effect name collisions with GADT constructors

Avoid naming GADT constructors `Pure`, `Lemma`, `Ghost`, `Stack`, `Tot`,
`GTot`, `Dv`, `St`, `Ex`, `ML`, `ALL`. These shadow effect names.
If unavoidable, use fully qualified `Prims.Pure`.

### W337: `@` without `open FStar.List.Tot`

F* issues Warning 337 when `@` (list append) is used without an explicit
`open FStar.List.Tot`.  The operator resolves to `FStar.List.Tot.append`
via deprecated special treatment.  Always add `open FStar.List.Tot` to
any module using `@`.

### Module-qualified names are NOT infix

Only operator symbols (`@`, `+`, `-`, `>>=`, `<|>`, etc.) can be used
in infix position (`a @ b`).  Module-qualified function names like
`L.append` MUST be used in prefix form (`L.append a b`), never infix
(`a L.append b` — this parses as `(L.append a) b`, which is valid F*
but means "apply a to L.append" rather than "append a and b").

### `open FStar.Seq` shadows `List.Tot.length` for `list` refinements

When both `open FStar.List.Tot` and `open FStar.Seq` are present,
bare `length` in type refinements on `list` resolves to `FStar.Seq.length`
(which expects `seq`, not `list`), producing Error 189:

```fstar
(* ERROR 189: Expected seq, got list *)
assume val hkdf_extract (salt: list byte) (ikm: list byte)
  : Tot (r: list byte {length r = 32})

(* CORRECT — fully qualified *)
assume val hkdf_extract (salt: list byte) (ikm: list byte)
  : Tot (r: list byte {List.Tot.length r = 32})
```

**Fix**: Use `List.Tot.length` or `L.length` explicitly on all `list`
refinements when `FStar.Seq` is in scope.  This applies to `.fsti`
files and any module that opens both libraries.

**Why it's subtle**: `.checked` cache files from prior `fstar.exe` builds
can mask this error — the full build may use a stale cache where
resolution happened differently.  Fresh LSP typechecking always reveals it.

### `open` order + name collisions between structurally-similar modules

When two modules define identically-named symbols (e.g., two Low* modules
both defining `O_None`, `tag_of`, `tag_to_type`, `lemma_roundtrip`),
the second `open` shadows the first.  In integration tests, this causes
Error 189 when the shadowed symbol's type doesn't match the expected type:

```fstar
open Foo.Low          (* defines O_None: opt_state *)
open Foo.Codec.Low    (* defines O_None: opt_c_tok — SHADOWS *)

let _test_low_opt : opt_state = O_None  (* ERROR 189: got opt_c_tok *)
```

**Fix**: Use fully qualified names in integration tests when both modules
are opened:
```fstar
let _test_low_opt : Foo.Low.opt_state = Foo.Low.O_None
let _test_clow_opt : Foo.Codec.Low.opt_c_tok = Foo.Codec.Low.O_None
```

Also applies to: `tag_of`, `tag_to_type`, `lemma_roundtrip`, `encode`,
`decode`, `O_Some` — any name shared between parallel Low* modules.

### `;` before `#pop-options` in Stack function — Syntax Error 168

`;` is the sequencing operator in F*.  The parser expects an expression
after `;`.  When the last expression in a Stack function body ends with
`;` and the next token is `#pop-options`, the parser sees `expr; #pop-options`
which is invalid — `#pop-options` is a directive, not an expression.

```fstar
(* BROKEN — trailing semicolon before #pop-options *)
#push-options "--z3rlimit 20"
let my_function ... : Stack unit ... =
  ... body steps ...;
  last_step arg1 arg2;  (* <--- THIS SEMICOLON *)
#pop-options

(* FIXED — remove trailing semicolon *)
let my_function ... : Stack unit ... =
  ... body steps ...;
  last_step arg1 arg2  (* no semicolon *)
#pop-options
```

Error 168 points at the `#pop-options` line, NOT the semicolon line.
The real bug is the `;` on the PREVIOUS expression.

See also: fstar-proofs §37 (full analysis with detection patterns).

### `if-then` without `else` in `C.Loops.for` callback body — Syntax Error 168

A `C.Loops.for` loop body is a function returning `Stack unit`.  When
the ENTIRE body is `if cond then expr` without `else`, F* reports
Error 168 because the function type `Stack unit` requires both branches
to return `unit`.

```fstar
(* BROKEN — if-then without else is the sole expression *)
let body (i: U32.t {...}) : Stack unit ... =
  if not (U8.eq (B.index buf i) (B.index expected i)) then
    B.upd result 0ul 0uy

(* FIXED *)
let body (i: U32.t {...}) : Stack unit ... =
  if not (U8.eq (B.index buf i) (B.index expected i)) then
    B.upd result 0ul 0uy
  else ()
```

The pattern `if cond then expr; next_thing` IS valid — `;` chains to
the next expression.  Only a bare `if-then` as the SOLE expression needs
an explicit `else`.

See also: fstar-proofs §38.

### `inline_for_extraction` + `: Tot U32.t` + bare `uint8_to_uint32` — Error 189

When combining `inline_for_extraction` with `: Tot U32.t` annotation and a
bare `uint8_to_uint32` (from `open FStar.Int.Cast`), F* may resolve the bare
name to the function TYPE (arrow), not the applied expression, causing
Error 189.  Use `FStar.Int.Cast.uint8_to_uint32` fully qualified.

```fstar
(* BROKEN — Error 189: bare name resolves to function type *)
inline_for_extraction
let u8_to_u32 (x: U8.t) : Tot U32.t = uint8_to_uint32 x

(* FIXED *)
inline_for_extraction
let u8_to_u32 (x: U8.t) : Tot U32.t = FStar.Int.Cast.uint8_to_uint32 x
```

Without the `: Tot U32.t` annotation: Error 56 (bound variable escapes).
With annotation but bare name: Error 189 (function type).
With annotation + fully qualified name: passes.

See also: fstar-lowstar §4.

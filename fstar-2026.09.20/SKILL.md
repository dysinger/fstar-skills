---
name: fstar-2026.09.20
description: F* v2026.09.20 — Custard extractor, Pulse, and the post-KaRaMeL toolchain. Use when working against F* ≥ 2026.09.20 (Low*/KaRaMeL stdlib removed; C extraction via Custard's Pulse rules, not LowStar.Buffer).
---

# F\* v2026.09.20 — Custard + Pulse (post-KaRaMeL)

> **Scope.** This skill is valid for F\* **≥ v2026.09.20** — the release that
> **removed the entire KaRaMeL/Low\* stdlib** (`FStar.HyperStack`,
> `FStar.HyperStack.ST`, `LowStar.Buffer`) and shipped **Custard**, a
> whole-program, demand-driven, monomorphizing extractor whose C backend emits
> direct C11 with **no karamel runtime**.
>
> For the older toolchain (Low\*, `Stack`, KaRaMeL `krml`, `FStar.Mul`,
> `op_Multiply`), see the `≤ 2025.12.15` sub-skills in this same repo:
> [`fstar-lowstar`](../fstar-lowstar/SKILL.md), [`fstar-build`](../fstar-build/SKILL.md),
> [`fstar-lang`](../fstar-lang/SKILL.md), [`fstar-proofs`](../fstar-proofs/SKILL.md),
> [`fstar-stdlib`](../fstar-stdlib/SKILL.md), [`fstar-docs`](../fstar-docs/SKILL.md).
> They are **pinned to F\* ≤ 2025.12.15** and are *not wrong*, just superseded
> by this document for the new surface.  The single index that routes both eras
> is [`SKILL.md`](../SKILL.md).
>
> Note: the `+lsp` in the flake pin `dysinger/fstar/v2026.09.20+lsp` is a
> **fork suffix** (that fork ports the LSP server onto the upstream base).  The
> *language and toolchain* surface described here is upstream `v2026.09.20`.

## 1. The toolchain delta (what vanished)

F\* `v2026.09.20` **deleted** the Low\*/KaRaMeL stdlib.  Code that namespaces
`FStar.HyperStack`, `FStar.HyperStack.ST`, or `LowStar.Buffer` **no longer
typechecks**.  Consequences for a roll-forward:

| Removed | Replacement |
|---|---|
| `LowStar.Buffer.buffer t` | `Pulse.Lib.Array.array t` (or `Pulse.Lib.Vec.vec t`) |
| `Stack` / `ST` effect | Pulse `fn` |
| `LB.upd` / `LB.index` | `b.(j) <- x` / `b.(j)` (Pulse `(.)`/`(.()<-)`) |
| `LB.as_seq h b` / `LB.length b` | the `pts_to` view `s : Seq.seq t` / `A.length b` |
| `modifies (LB.loc_buffer b) h0 h1` | Pulse separation-logic pre/post |
| `FStar.HyperStack.ST.get ()` (`h_mid`) | *gone* — no heap capture; use `pts_to` views |
| `open FStar.Mul` (for `*` as multiply) | **module deleted**; `*` is natively multiplication |
| `Prims.op_Multiply a 10` | `a * 10` |
| `--split_queries always` | option removed; F\* emits one SMT query per obligation |
| `krml` / `--codegen krml` / wasm backend | deleted; only Custard remains for C |
| OCaml `--codegen OCaml` batch mode | **one source file per invocation** (Error 10) |

The floating `+lsp` fork (`dysinger/fstar`) exists only to keep the LSP server
and is otherwise the upstream `v2026.09.20` compiler.

## 2. Custard: the only remaining C-extraction path

Custard (`--codegen Custard`) extracts **Pulse** (`fn`,
`Pulse.Lib.Reference`/`Vec`/`Array`/`Box`/`ArrayPtr`), **not** the old Low\*
style.  Its C backend emits direct C11 (only `<stdint.h>`, `<stdlib.h>`,
`<stdbool.h>`, `<string.h>`; `typedef uint8_t custard_unit;`) and compiles with
`-Wall -Wextra -Werror`.

### Backend enum (authoritative)

`--custard_backend` accepts exactly **`OCaml` (default) | `FSharp` | `KrmlC` |
`KrmlRust` | `C`**.  There is **no wasm**.  Status as of this writing:

| Backend | Notes |
|---|---|
| `OCaml` | legacy ML; monomorphic-only for C-like layout |
| `C` | direct C11, **no karamel**; requires `--custard_monomorphize_types true` |
| `KrmlC` / `KrmlRust` | karamel re-ingest; `KrmlRust` broken upstream (431 rustc errors, no `lowstar` module) |
| `FSharp` | `.NET 10`; separate follow-up |

### Required flags for direct C

```bash
fstar.exe --codegen Custard \
  --custard_backend C \
  --custard_monomorphize_types true \
  --custard_entry_module <Mod> \     # library mode (no main)
  --odir out <Mod>.fst
```

- **`--custard_monomorphize_types true` is mandatory for `--custard_backend C`**
  (C has no type variables → no `Obj.t` fallback).
- **`--custard_entry_module`** roots *every top-level definition* of a module —
  this is library mode (the other backends call it `--extract_module`).
  `--custard_main` names a `main : unit -> Int32.t` to *invoke* on startup;
  `--custard_entry` names a *single* root.

  **Export-surface gotcha (don't re-claim "N fns exported").** With
  `--custard_entry Data.Codec.Pulse.encode_bytes --custard_entry
  Data.Codec.Pulse.decode_bytes`, the emitted `fstar_codec.h`/C file exports
  **only those two named roots** — the individual `encode_token`/`decode_token`/
  `encode_uint8`/… leaf functions are **not** independently callable, and the
  roundtrip `Lemma`s are erased in any case.  A claim like "18 API fns + 9
  roundtrip lemmas exported" is **false** for a single-root build; the only
  exported surface is the dispatch pair (plus whatever `type`s the roots need).
  If the *full* surface must be exported, use `--custard_entry_module`, and
  then `noextract`-guard every spec-only def you don't want rooted (see §3).

- A **library has no `main`** — use `--custard_entry_module`, not
  `--custard_main`.

### C layout choices

- record → `struct`; all-nullary constructor variant → `enum`;
  single-constructor variant → plain `struct` (no tag/union; keeps tuples/1-ctor
  records free); anything else → tagged union (`enum tag` + `union`).
- matching → **if/else-if chain** (not `switch`) — so a tagged union return
  (e.g. `decode_result_c`) is fine: no struct-return trap.
- constructor applications → C99 compound literals with designated initializers.
- `decode_result_c` (tagged union) **returns by value cleanly** — no out-param
  refactor needed (that was the *old* wasm limitation).

## 3. Pulse idiom (verified 0-admit, extracted to clean C11)

The module skeleton for a Pulse leaf:

```fstar
module Data.Codec.Low
#lang-pulse

open Pulse
open Pulse.Lib.Reference
module A = Pulse.Lib.Array
module US = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq
open FStar.Seq
open FStar.Int.Cast
```

- **Buffer type**: `A.array U8.t` (prefer `Array` over `Vec` — simpler, same
  `SizeT.t` indices).  Heap view is `A.pts_to b s` where `s : Seq.seq U8.t`
  (erased).  `A.pts_to_len b` (ghost) recovers `A.length b == Seq.length s`.
- **Read/write**: `b.(j)` / `b.(j) <- x` — `j : SizeT.t`.  Convert a `U32.t`
  offset with `US.uint32_to_sizet i`.
- **Public API stays `U32.t`** for offsets/`pos`/`n`/`value` (matches the pure
  spec + OCaml extraction); only the buffer read/write boundary uses `SizeT`.

### The three rules that cost the most time

1. **Bounds live in TYPES (refinements), not `pure` preconditions.**  A
   `pure (...)` fact in `requires` is **NOT** available while typechecking the
   `ensures` clause or a body `Seq.index`/`Seq.slice` term.  For a
   self-contained `ensures`, use `A.length b` (a pure `Ghost nat`, always in
   scope) for bounds, and re-assert `A.length b == Seq.length s` inside the
   `pure`.  The canonical pattern is `Pulse.Lib.Array.PtsToRange.pts_to_range_index`
   (bounds as `Ghost.erased nat` implicit args).
2. **Never use `U32.v` / `U8.v` / nat `%` in extracted bodies** — `Prims.int`
   has no C representation (Error 368).  Use `FStar.Int.Cast` narrow/widen
   casts: `uint32_to_uint8`, `uint8_to_uint32`.  `U32.v` is fine in specs/`pure`
   (erased).
3. **`U32.add i k` needs an overflow precondition** `U32.v i + k < 4294967296`
   in `requires` (the analogue of the old `lemma_u32_add_no_overflow`).

### Spec functions must be `noextract`

Pure spec helpers (`varint_encode_pred`, `varint_decode_expected`) reference
`Seq`/`Prims.int` and are rooted by `--custard_entry_module`.  Mark them
`noextract` so Custard skips them (it "passes over silently" `noextract` roots)
— otherwise Error 368 (`Prims.int` has no C representation).

### Making the post-multibyte cases prove

`word32be`/`word32le` encoders must use **`U32.div`/`U32.rem`** (not
`U32.shift_right`) so the byte extraction *syntactically* matches the pure
`*.enc` division structure (`v / 16777216`, `(v / 65536) % 256`, …).  Shifts
would require the old `lemma_word32_shift_bytes` bridge (which is now gone).

### Roundtrip lemmas are *easy* (unexpectedly) — **EXCEPT varint**

Because the pure `codec` record's `.enc`/`.dec` are **computable projections**,
`dec (enc x)` reduces to `Inr (x, n)` and SMT discharges the roundtrip lemma
automatically — no `lemma_word32_shift_bytes`, no `h_mid` heap threading.
The `token`/`byteval`/`uint8`/`word16*`/`word32*` roundtrip lemmas verify with
zero manual frame reasoning.  `word32be`/`word32le` are *rlimit-sensitive* but
terminate (slow, ~90s each at `--z3rlimit 120`).

**`varint` is the exception — it is a NON-TERMINATING SMT query, not "easy".**

`encode_varint`/`decode_varint` are **hand-inlined** (not `varint.enc`/`.dec`
projections).  `lemma_pulse_roundtrip_varint` composes the two, and the single
(per-`fn`) SMT query must discharge the 5-way threshold split (`<128`, `<16384`,
`<2097152`, `<268435456`, else) through the nested `% 128` / `/ 128` byte
extraction **plus** U32 `U32.add`/`U32.mul` reconstruction.  Z3 spins at 100%
CPU forever — it does **not** time out cleanly, and raising `--z3rlimit` (tested
up to 800) does **not** help: the query is undecided by the solver, not merely
under-budgeted.

### Fix: SMTPat structural lemma for the varint roundtrip

Lift the per-length div/mod decomposition out of the hot query with a pure
`noextract` `Lemma` carrying an `[SMTPat …]` trigger.  The pure module already
exports `lemma_varint_2byte_arithmetic` … `lemma_varint_5byte_arithmetic`
(`Data.Codec.Types`) proving `n = 128*(n/128) + n%128` and the multi-byte
analogues.  The Pulse module adds:

```fstar
noextract
let lemma_varint_roundtrip_smtpat (v: U32.t) (s: Seq.seq U8.t) (i: U32.t)
  : Lemma
    (requires varint_encode_pred (U32.v v) s (U32.v i) /\
              U32.v i + nbytes_of_varint (U32.v v) <= Seq.length s)
    (ensures varint_decode_expected i (U32.uint_to_t (nbytes_of_varint (U32.v v))) s
             == DR_Inr ({ n = U32.uint_to_t (nbytes_of_varint (U32.v v)); value = v }))
    [SMTPat (varint_decode_expected i (U32.uint_to_t (nbytes_of_varint (U32.v v))) s)]
  =
  let n = U32.v v in
  if n < 128 then ()
  else if n < 16384 then DC.lemma_varint_2byte_arithmetic n
  else if n < 2097152 then DC.lemma_varint_3byte_arithmetic n
  else if n < 268435456 then DC.lemma_varint_4byte_arithmetic n
  else DC.lemma_varint_5byte_arithmetic n
```

Rules learned (2026.09.20 era):

1. **`--custard_entry_module` roots every top-level def** (reachable **or not**).
   "Only what's in the execution path extracts" is only true for
   `--custard_entry`/`--custard_main` (single-root demand).  For library mode
   (`--custard_entry_module`) the only shield is **`noextract`** — mark every
   spec-only `Lemma`/helper `noextract` or Custard roots it and Error 368 fires.
   A pure `Lemma` body is *also* erased (proofs are `unit`-valued), so it is
   doubly shielded, but `noextract` is what actually stops the rooting.
2. **A pure `Lemma` does NOT fire inside a Pulse `fn` unless SMTPat-triggered.**
   Merely defining the lemma (or even `let _ = lemma …` on the *wrong* buffer)
   leaves the `fn`'s post unproven.  The trigger must match the *exact* term
   SMT sees: here `varint_decode_expected i m s1` where `m` unifies to
   `U32.uint_to_t (nbytes_of_varint (U32.v v))` via `encode_varint`'s post
   `U32.v m == nbytes_of_varint (U32.v v)`.
3. **The hang is z3 at 100% CPU, not 0%.**  The AGENTS.md "0% CPU / `stopped`"
   heuristic is the *older* symptom.  This varint query blazes at ~100% CPU for
   minutes (`ps -o pcpu=,time=` cumulapes 1s CPU per 1s wall) and never returns;
   it is not a `stopped`/`S` zombie and is not "still working" either — it is
   undecidable-in-practice.  Treat *both* 0%-stopped and 100%-spinning-anomalously-long
   as hangs; bisect rather than wait.
4. **Bisecting a `#lang-pulse` module by truncation is off-by-one prone.**
   `decode_bytes`'s body-closing `}` is NOT its last `}` — the `match c { … }`
   and the body `{ … }` are two separate depths, so `head -N` at the wrong `N`
   leaves `brace depth == 1` and F\* reports a bare `Syntax error` at EOF.  Count
   `{}`/`()` balance (a 10-line Python scanner that skips `(* … *)`) before each
   truncation; the green cut points for this module are (encoders+decoders)
   `head -719`, (+dispatchers) `head -863`, (+through word16le) `head -974`, etc. —
   **never** `head -862`.
5. **`varint_decode_expected`/`varint_encode_pred` remain `noextract`** even
   with the SMTPat lemma added; the lemma itself is `noextract` and references
   `Seq`/`Prims.int`, so it must not be rooted.
6. **Comment line *positions* in the varint region are SMT-fragile — observed
   correlation, mechanism unproven.**  Collapsing the fragmentary `(** … *)`
   one-liner comments around `nbytes_of_varint` / `lemma_nbytes_of_varint_bound` /
   `lemma_varint_*byte_arithmetic` in `Data.Codec.Types` into single coherent
   blocks **correlated with** `Data.Codec.Pulse`'s varint roundtrip becoming a
   non-terminating z3 spin (reproduced 4× in one session, ~100% CPU, `ps` shows
   no `stopped` state; reverting the collapse restored GREEN).

   The *mechanism* is not established: the plausible reading is that the
   edit perturbs the `[SMTPat (varint_decode_expected i (U32.uint_to_t
   (nbytes_of_varint (U32.v v))) s)]` trigger's unification, but SMTPat triggers
   are term-structural, not line-number-dependent, so "line numbers → z3 spin"
   is an **observed correlation, not a verified rule** (cache/source-position
   perturbation is an alternative explanation).  **Practical rule:** treat any
   edit near the varint arithmetic lemmas as requiring a re-verify, and don't
   bulk-collapse that region's comments as a drive-by "cleanup" — but don't
   enshrine it as an immutable mechanism.  (The non-varint stacked fsdoc
   collapses — `nat_of_int`, `u32_of_nat`, `mk_decode_error`,
   `string_is_ascii`, `u32_of_small_nat` — are safe and landed.)

## 4. Build / nix wiring for the new toolchain

The Pulse stdlib ships **inside the install**, under
`$(fstar.exe --locate_lib)/pulse`.  The include chain it needs (when the
Makefile uses `--no_default_includes`):

```
--include $lib/fstar/pulse/common          # Pulse.Lib.Core, Pulse.Main (fsti)
--include $lib/fstar/pulse/common.checked
--include $lib/fstar/pulse/pulse/lib       # Pulse.Lib.Array, Pulse.Lib.Vec, …
--include $lib/fstar/pulse/pulse.checked
```

- Skip re-verifying the Pulse stdlib with
  `--already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore`.
- **Seed the `--cache_dir`** with pre-verified `*.checked` (from the
  `fstar-checked` "ulib.checked" artifact) or Error 317 ("Expected Prims to be
  already checked") fires.
- `--codegen OCaml` now needs **one source file per invocation** (Error 10), and
  the dependencies' `.checked` files loaded (verify in dependency order, then
  extract with `--include cache`).
- The word32 roundtrip lemmas **time out at low rlimit**; use `--z3rlimit 120`
  (they pass at 120, deterministically time out at the default/80).
- OCaml is `ocaml-ng.ocamlPackages_5_3` (5.3, **not** 5.4).
- `karamel` is **fully removed** — it was an in-tree F\* submodule used only to
  install `krml`; neutralize the `make -C karamel install` step with a no-op
  `karamel/Makefile` + `FSTAR_USE_KRML_EXE=1`.
- **Exposing the overlay's `z3` back out as a top-level attr overflows the nix
  fixpoint.**  The F\* flake derives z3 from the fork's tree via
  `z3 = prev.callPackage (inputs.fstar + "/.nix/z3.nix") {}` (pins z3 4.13.3,
  the version the bootstrap needs — plain `pkgs.z3` from the same nixpkgs rev
  is **4.16.0**, the wrong one).  If you `inherit z3` from that overlay so a
  `devShells.default.buildInputs` can list it, `nix develop` (and any build
  consuming that attr) fails with `error: stack overflow; max-call-depth
  exceeded` while evaluating `buildInputs` — the overlay's `callPackage`
  self-references once the attr is folded back into the fixpoint.  **Don't**
  re-export overlay-internal derivations.

  The z3 is already reachable without a separate attr: the `fstar.exe` install
  wraps the binary with `wrapProgram … --prefix PATH "" "${z3}/bin"`, so
  `make check` / `fstar.exe` (and anything launched from the devShell) already
  finds the correct z3 on the `fstar.exe`'s own PATH.  For the devShell, add
  `git` + the `dotnet` SDK (for the F# target) but **not** a bare `z3`.
- `dotnet-sdk_10` (underscore attr) **does** exist in nixpkgs rev `c31cf09…`
  (resolves to `dotnet-sdk-wrapped-10.0.300`); the earlier worry that the
  pinned 24.11-era snapshot predates `.NET 10` was wrong.  Reachability of the
  `dysinger/fstar` fork pin (`cf847952b97a5f392ebd8c097e9f548fa93d769a` at
  `refs/heads/v2026.09.20+lsp`) is also confirmed via `git ls-remote` — both
  reproducibility landmines turned out to be non-issues.

## 5. Common errors in the new surface

| Error | Meaning | Fix |
|---|---|---|
| 19 (timeout, word32 roundtrip) | low z3 rlimit | `--z3rlimit 120` |
| 317 | `--already_cached X` but cache lacks `X.fst.checked` | seed cache with stdlib `.checked` |
| 368 | `Prims.int` reached extraction | `noextract` the spec fn; `FStar.Int.Cast` in bodies |
| 134 / 285 | `Pulse` namespace not found | add the four `pulse/*` `--include` paths (or drop `--no_default_includes`) |
| 180 (`Unexpected operator **`) | `#lang-pulse` not active | load the Pulse lib (`open Pulse`); ensure `#lang-pulse` + Pulse includes |
| 10 | OCaml codegen batch of many files | one file per `--codegen OCaml` run |
| 66 (implicit `p` only in pre/post) | `FStar.Classical.forall_intro_2/3/4` predicate not inferable | annotate `#a`/`#b`/`#p` explicitly (see §8) |
| — (hang, varint roundtrip) | 100% CPU z3, non-terminating `lemma_pulse_roundtrip_varint` | SMTPat structural lemma (see §3) |

## 6. Backend matrix (as verified this session)

| Backend | Mechanism | Status |
|---|---|---|
| `ocaml` | `--codegen OCaml` (legacy ML) | ✅ pure spec extracts (no Pulse needed) |
| `native` (C) | `--custard_backend C` (direct C11, no karamel) | ✅ Pulse leaf extracts + compiles |
| `fsharp` | `--codegen FSharp` / `--custard_backend FSharp` | 🟡 `.NET 10`, separate follow-up |
| `rust` | `--custard_backend KrmlRust` → karamel | ❌ dead upstream |
| `wasm` | — | ❌ gone (no backend) |

## 7. Formatter, keyword, and proof-engineering gotchas (learned the hard way)

### The F\* formatter is broken upstream — do **not** wire it into treefmt

There is **no reliable F\* auto-formatter** in `v2026.09.20+lsp`.

- `fstar.exe --print` / `--print_in_place` **rewrite `(* … *)` inline comments
  into `//` line comments**, which F\* cannot parse (Error 168 — `//` is not a
  comment in F\*, only `(* *)` and `///`).
- They also **lower-case hex literals** (`0x6Cuy` → `0x6cuy`) and restructure
  code (collapse `if/else` chains onto one line).
- `--print`, `--print_in_place`, and the `fstar.exe --ide` `format` query all
  **crash with "Pattern matching failed" in `FStarC_Parser_ToDocument.ml`** on
  `#lang-pulse` modules (line 932 of the compiled `fstarc.ml`).  The `--ide`
  `format` query also *stalls* on larger pure modules.

**Consequence:** leave `.fst`/`.fsti` hand-formatted.  For `treefmt.nix`, format
only nix (and skip the F\* files, documenting why).  The same applies to
prettier on prose markdown — it churns legal/changelog docs and hand-written
prose (double-space sentence gaps, `*`/`F*` emphasis).

### `label` is a **reserved Pulse keyword**

A `#lang-pulse` module cannot use `label` as a combinator name OR a record
field name (`{ …; label = … }` or `{ r with label = … }`) — the parser rejects
it with a bare `Syntax error`.  Concretely: a codebase whose pure spec defines
`label : string -> codec a -> codec a` and a `decode_error` record with a
`label` field **cannot** mix those pure definitions into a `#lang-pulse` module.

**Fix:** split pure tests/definitions (that use `label`) into a plain module,
and put only the buffer-based code into a dedicated `#lang-pulse` module.  Do
not try to `open` the `label`-bearing module from `#lang-pulse`.

### `Pulse.Lib.Array.alloc` / `.free` are deprecated but functional

`A.alloc x n` / `A.free a` carry `[@@deprecated "…unsound; only use for model
implementations"]` (Warning 288) but **verify green and extract** — they are the
Pulse analogue of the old Low\* `alloca`+`push_frame`/`pop_frame`.  The
non-deprecated scoped form is `A.with_local init len (fun arr -> body)`, but its
signature (universe-polymorphic `ret_t` + `pre`/`post` slprops) is finicky to
call directly; `alloc`+`free` is the pragmatic choice for a scoped buffer test
(the deprecation is a warning, not an error, and does not gate the build).

### `assert_norm` does **not** reduce `let`-bound variables

`assert_norm (x == E)` reduces the *term* on each side, but a `let x = … in`
binding is a free variable whose definition is not substituted into the
`assert_norm` redex.  So

```fstar
let expected = string_to_bytes "ABC" in
assert_norm (expected == seq_of_list [0x41uy; 0x42uy; 0x43uy])  -- FAILS
```

but the inlined form succeeds:

```fstar
assert_norm (string_to_bytes "ABC" == seq_of_list [0x41uy; 0x42uy; 0x43uy])
```

This is because `string_to_bytes` ultimately calls `FStar.String.list_of_string`,
which only reduces on a *literal* string, and `assert_norm` only normalizes
closed terms.  When a `Lemma`'s body is failing at rlimit 40 with an
`assert_norm` on a `let`-bound var, inline the `let`.

### 100% lemma coverage: anchor every public `Lemma`

A "coverage anchor" module (`let _x = f` for every public def) is how you prove
nothing is dropped.  To audit it:

```bash
# source defs (strip prefixes, unqualified)
grep -hoE '^(let|let rec|fn|type|val)[[:space:]]+[a-zA-Z_][a-zA-Z0-9_]*' src/*.fst \
  | sed -E 's/^[a-z ]+//' | sort -u > /tmp/defs
# anchored final identifiers (last .segment of each `let _X = RHS`)
grep -oE '^let _[a-zA-Z0-9_]+ = .*' test/Data.Codec.Test.Integration.fst \
  | sed -E 's/^let _[a-zA-Z0-9_]+ = //; s/[. ]*\(.*$//; s/[. ]*$//; s/^.*[."'"'"' ]//' \
  | sort -u > /tmp/anchored
comm -23 /tmp/defs /tmp/anchored | grep '^lemma_'   # the real gap
```

Every uncovered `lemma_*` is a genuine coverage hole (the combinator
"refinement" lemmas — `lemma_product_*`, `lemma_map_*`, `lemma_byte_val_*`,
`lemma_digits_to_int_*`, `lemma_choice_c1_dominates`, `lemma_one_of_*`,
`lemma_scan_until_*`, `lemma_take_until_*` — are the common misses).  A bare
`let _x = f` anchor typechecks without discharging VCs, so it is a pure
"exists + typechecks" check; that's the point.

## 8. v2026.09.20 stdlib + termination deltas (new-session learnings)

### Arithmetic `decreases` clauses are BROKEN — use a bare variable or list subterm

Writing a subtraction in a `decreases` clause fails to parse in v2026.09.20:

```fstar
let rec go (i: nat) ... : nat (decreases (n - i)) = ...  -- ERROR 208
  (* Unexpected term: ((decreases (-(n, i)))) *)               -- parsing bug
```

The `-` between two nats inside `decreases (…)` is parsed as a *(negated)
tuple*, not subtraction — a v2026.09.20 parser regression.  (`decreases n` and
`decreases (n + 1 - k)` written *bare* also error the same way.)  The working
forms, matching `fstar-codec`:

```fstar
let rec pow2 (n: nat) : Tot int (decreases n) = ...           -- bare nat
let rec bytes_decode (bs: list byte) ... (decreases bs) = ... -- bare list/subterm
```

**Rule:** recurse on a *bare* `nat` or on the *subterm of a list/tuple* (F\*'s
structural order), and return `Tot` — `: Tot (option elem) (decreases ls)`.  Do
NOT use `Seq.length s - i` or any arithmetic in `decreases` on this toolchain.

**REFINEMENT (verified 2026-10-03, `Data.Image.PNG.Filter`):** the parser
regression fires on a *bare-variable* `n - i` only.  `decreases (length l - i)`
where `length l` is a **function application** (`List.Tot.length l`, not a bare
`n`) parses and verifies fine — used 4× in `lemma_sub_rt`/`lemma_up_rt`/
`lemma_average_rt`/`lemma_paeth_rt` (each `(decreases (length row - i))`,
recursing on `i+1` guarded by `i < length row`).  So: bare `n - i` = ERROR 208;
`f l - i` (a call minus a var) = OK.  Prefer these anyway only when you need
index-recursion; list-subterm recursion is still the safer default.

### Wrapping byte arithmetic roundtrip — `U8.t` is OPAQUE, bridge via `v`/`v_inj`

`FStar.UInt8.t` is declared `new val t : eqtype` (opaque), **NOT**
definitionally equal to `FStar.UInt.uint_t 8` (`x:int{size x 8}`).  So
`FStar.UInt.lemma_add_sub_cancel #8 a b` (typed over `uint_t n`) does **not**
unify with `U8.t` arguments.  The `+`/`-` operators on `U8.t` are the
*bounds-respecting* `add`/`sub` (refined, require `size (v a + v b) 8` — SMT
cannot discharge for symbolic `a b`).  For **wrapping** arithmetic use
`FStar.UInt8.sub_mod` / `add_mod` explicitly, and prove the roundtrip identity
at the `v` level then lift with `v_inj`:

```fstar
open FStar.UInt8
let lemma_wrap (a b: t) : Lemma (add_mod (sub_mod a b) b == a) =
  FStar.UInt.lemma_add_sub_cancel #8 (v a) (v b);   (* over uint_t 8, i.e. int{size .. 8} *)
  v_inj (add_mod (sub_mod a b) b) a                  (* v_inj : v x == v y ==> x == y *)
```

`lemma_add_sub_cancel #n a b : Lemma (add_mod (sub_mod a b) b == a)` and its
dual `lemma_sub_add_cancel #n a b : Lemma (sub_mod (add_mod a b) b == a)` are in
`FStar.UInt.fsti` (~line 592).  The PNG filter roundtrips (Sub/Up/Average/Paeth)
all collapse to exactly this identity — the *predictor* value is irrelevant to
its own inverse: `(x - p) + p == x` for ANY byte `p`.

### `FStar.List.Tot` has **NO** `take`/`drop` — they live in `FStar.Sequence`

`FStar.List.Tot.Base` exports `nth`/`index`/`rev`/`append`/`mapi`/`fold_left`
etc., but **not** `take` or `drop` (those are `FStar.Sequence.Base.take`/
`drop` over `Seq`, not `list`).  For list proofs needing a prefix/suffix, define
your own (transparent, structural — they verify via plain recursion):

```fstar
let rec take (l: list a) (n: nat) : Tot (list a) (decreases n) =
  if n = 0 then [] else match l with [] -> [] | x::xs -> x :: take xs (n-1)
let rec drop (l: list a) (n: nat) : Tot (list a) (decreases n) =
  if n = 0 then l else match l with [] -> [] | x::xs -> drop xs (n-1)
```

(The `decreases n` — a *bare* nat — is the safe form; see above.)

### `Seq.fold_left` / `Seq.count` are GONE — convert to a list first

The post-KaRaMeL `FStar.Seq` (`FStar.Seq.Base`/`FStar.Sequence`) no longer
exports `fold_left`/`fold_right`/`count` directly.  To fold or count over a
sequence, convert with `Seq.seq_to_list` and use `FStar.List.Tot`:

```fstar
let count (x: elem) (s: Seq.seq elem) : nat =
  List.Tot.count x (Seq.seq_to_list s)      -- List.Tot.count : #a:eqtype -> a -> list a -> nat
```

(`List.Tot.count`/`List.Tot.fold_left`/`List.Tot.filter` are what you use; the
`Seq` module has `map_seq`, `init`, `slice`, `seq_to_list`, `seq_of_list`, but
no fold/count.)

### `Seq.seq_to_list` head does NOT relate to `Seq.index 0` — bridge explicitly

`Seq.seq_to_list s`'s head is **not** SMT-equal to `Seq.index s 0` — a bare
`Lemma` with `= ()` does NOT discharge it (both are opaque projections).  A
list-level run scanner whose `rest_cond` framing is sequence-level
(`Seq.length r = 0 \/ not (f (Seq.index r 0))`) needs this explicit bridge (via
the transparent stdlib uncons laws):

```fstar
(** Lemma: the head of [Seq.seq_to_list s] is [Seq.index s 0] (non-empty). *)
let lemma_seq_to_list_head_is_index (s: byte_seq) : Lemma
  (requires Seq.length s > 0)
  (ensures (match Seq.seq_to_list s with
            | [] -> False
            | hd :: _ -> hd == Seq.index s 0))
  =
  let hd = Seq.index s 0 in
  let tl = Seq.slice s 1 (Seq.length s) in
  FStar.Seq.Properties.lemma_split s 1;       (* s == cons (index s 0) (slice s 1 len) *)
  FStar.Seq.Base.lemma_seq_to_list_cons hd tl; (* seq_to_list (cons h tl) == h :: seq_to_list tl *)
  ()
```

This is the same class as `lemma_seq_to_list_of_list_append` (the §11 bridge):
`seq_to_list` only unfolds through `FStar.Seq.Base.lemma_seq_to_list_cons`/
`FStar.Seq.Properties.append_cons`/`lemma_split`, never by SMT alone.  The
`satisfy_many0`/`satisfy_many1` generic roundtrip (fstar-codec, 0-admit) chains
`lemma_seq_to_list_of_list_append xs r` (prefix) with
`lemma_seq_to_list_head_is_index r` (suffix head) so the symbolic-`f` framing
reaches the list-level scanner `satisfy_run_scan`.

### `Tot` does NOT block extraction — *pure types* do

A common fear when porting to C: "if I write `Tot`, can Custard still extract
C/OCaml/F#?".  Yes — `Tot` is fine (it is the dominant convention in xeno,
~1000 uses).  What actually gates each backend is the *types in runtime bodies*:

| Module kind | Traits | Extracts to |
|---|---|---|
| pure spec (`Seq`/`list`/`nat`/`int`, `Tot`, `Lemma`) | no C repr | **OCaml only** (`--codegen OCaml`) |
| Pulse leaf (`fn`, `U32.t`/`U8.t`, `A.array`, `Int.Cast`) | C-safe | **C + OCaml + F#** (Custard) |

The Pulse leaf's *spec* (in `ensures`/`noextract` helpers) may mention `Seq`/
`find_candidate` (erased), but its *runtime body* must stay in `U32.t` + `A.array`
+ Pulse primitives.  This is exactly `fstar-codec`'s split: `Data.Codec.Types`
/`Data.Codec` → OCaml; `Data.Codec.Pulse` → C/OCaml/F#.

### Local sibling flake deps: `git+file:///abs/path`, not `path:../`

When a new repo consumes a *local sibling* flake (e.g. `fstar-basen` →
`../fstar-codec`), `path:../sibling` resolves fine as a URL but **fails during
`nix flake lock`** (`error: '...' is too short to be a valid store path` / pure-
eval path restriction).  Use `git+file:///absolute/path/to/sibling` instead — it
locks to the sibling's HEAD commit; switch to the published
`github:<owner>/<repo>` input when the repo ships.

### `FStar.Classical.forall_intro_2` (and `_3`/`_4`) needs explicit implicit args (Error 66)

Under v2026.09.20, a bare `FStar.Classical.forall_intro_2 f` where `f` returns a
`Lemma` fails to resolve its implicit predicate `#p` (and dependent `#b`):

```fstar
(* FAILS — Error 66: Failed to resolve implicit argument ?52 of type
   x: char -> _: list byte -> prop, introduced for Instantiating implicit
   argument 'p'.  "This implicit argument only occurs in a pre- or
   postcondition, so it cannot be inferred." *)
FStar.Classical.forall_intro_2 (fun c rest -> lemma_utf8_decode_prefix c rest)
```

The single-argument `forall_intro` (`#a #p f`) is usually still inferred, but
`forall_intro_2` has a *dependent* `#b : a -> Type` followed by
`#p : x:a -> b x -> prop`, and neither can be recovered from a lambda whose
`Lemma` body only mentions `p` in its post-condition.  Fix: annotate all three
implicits explicitly:

```fstar
FStar.Classical.forall_intro_2
  #FStar.Char.char
  #(fun (_: FStar.Char.char) -> list byte)          (* the dependent b *)
  #(fun (c: FStar.Char.char) (rest: list byte) ->
       utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  (fun c rest -> lemma_utf8_decode_prefix c rest)
```

That is: write out `#a`, `#b` (as a `fun _ -> T` lambda), and `#p` (the exact
`ensures` proposition) rather than letting SMT recover them from the lemma
type.  `forall_intro_3`/`forall_intro_4` are the same shape (one more `#b` per
quantifier).  The reference repos (`fstar-codec`, `fstar-basen`, `fstar-text`)
avoid `forall_intro_2` entirely, but if you need it, this is the working form.

### Downstream-repo OCaml extraction: extract the dep's pure spec locally, not the wrapped `codec-ocaml`

A repo that *depends* on `fstar-codec` (e.g. `fstar-basen`, `fstar-text`) and
wants its own `ocaml` target hits a cross-repo module-resolution trap.  The
`fstar-codec` flake's `ocaml` package (findlib `codec-ocaml`) **wraps** its
modules into a `Codec.*` namespace (dune `(wrapped true)` default), so the
extracted `.ml` files of the downstream repo — which reference the *bare*
top-level `Data_Codec_Types` / `Data_Codec` — fail with:

```
File "Data_BaseN_Base32.ml", line 2: Error: Unbound module Data_Codec_Types
```

Do **not** `(libraries fstar.lib codec-ocaml)` the downstream into the wrapped
package.  Instead, in the downstream's `ocaml-src` derivation, **extract the
codec's pure spec (`Data.Codec.Types` + `Data.Codec`) locally** via
`--codegen OCaml` from the `codec-src` flake input, compile those `Data_Codec_Types.ml`
/`Data_Codec.ml` into the downstream's own dune library (unwrapped), and drop the
`codec-ocaml` findlib dep:

```nix
# in ocaml-src buildPhase, before extracting your own pure modules:
for m in Data.Codec.Types Data.Codec; do
  ${fstar-exe} --no_default_includes --include "$ULIB" --include ${codec-src}/src \
    --cache_checked_modules --cache_dir cache --odir cache ${codec-src}/src/$m.fst || exit 1
  ${fstar-exe} … --codegen OCaml --odir $out ${codec-src}/src/$m.fst || exit 1
done
# dune: (modules …your-modules… Data_Codec_Types Data_Codec Custard)
#        (libraries fstar.lib)   ← NO codec-ocaml
```

No `Custard` collision: you only extract the codec *pure* spec, never its
Pulse leaf (the leaf is what emits `Custard.ml`).  This is the same
"compile the codec spec locally, unwrapped" shape `fstar-codec` itself uses
(there `pure-modules` *is* the codec spec).

## 9. Extracted-repo uniformity (verified 2026-10-03, all 7 repos + template)

When a package is extracted to a standalone `fstar-<pkg>` repo, the repo MUST be
on par with its siblings — not partially uniform, but fully.  Audit **every
file in every repo** against this checklist (this was the source of two rounds
of "make it uniform" churn this session):

### Byte-identical across all repos (do not diverge)

- `.gitignore` — identical string every repo (covers `out/`, `result*`, `cache`).
- `treefmt.nix` — identical (formats **nix only**; `.fst`/`.md` are deliberately
  excluded because the F\* formatter is broken upstream, see §7).
- `LICENSE.md` — the AGPL body after the name blurb is byte-identical.

### Uniform-with-per-package-name files

- `LICENSE.md` blurb — the exact pattern is `<name> — a formally verified
  <desc> written in F\*.` (`codec` uses a comma + "framework" as the origin;
  every other repo says "a formally verified <desc> library written in F\*.").
  Do NOT drift to "a verified … that extracts to C/OCaml/F# via Custard" —
  that was the template's phrasing and leaked into an extracted repo.
- `CHANGELOG.md` — MUST exist in **every** repo (library **and** `fstar-nix-flake-template`).
  Keep-a-Changelog + SemVer, with `## [Unreleased]` and `## [0.1.0] — initial
extraction` (package-accurate `### Added` module lists).  `fstar-codec` is the
  reference; the other six shipped without one until this session.
- `flake.nix` `description` — `"<name> — verified <desc>"`; inputs
  `nixpkgs`/`flake-utils`/`treefmt-nix`/`fstar`(pin `v2026.09.20+lsp`) uniform,
  plus per-package `fstar-*` dep inputs.
- `default.nix` — deliverable set is ALWAYS `{ checked; ocaml; native; fsharp; }`;
  `pname` drops the `fstar-` prefix; codec dep injected as `codec-src`/`codec-checked`.
- `Makefile`, `AGENTS.md`, `API.md`, `README.md` — header/structure uniform;
  README/API content is package-specific (architecture, RFC coverage, module tables).
- Copyright/SPDX header — `Copyright 2026 Department of Code LLC.` +
  `SPDX-License-Identifier: AGPL-3.0-or-later` on every `.fst`/`.nix` (and `.md` where used).

### Gotchas

- **No scratch dirs in a shipped repo.**  `fstar-codec` carried a `spike/` and
  `openspec/` dir that no other repo has — a uniformity violation (scratch
  `.fst`/`.c`/`.checked` and old change proposals).  Flag and confirm before
  deleting (Mandate 23 backup-before-destroy).
- **HTTPS remotes + `osxkeychain`.**  Set `origin` to `https://github.com/dysinger/<repo>.git`
  (not `git@github.com:…`) and `git config --global credential.helper osxkeychain`
  so pushes don't prompt for SSH passwords.  The first HTTPS push caches a PAT.

### 100%-lemma-coverage audit — the `comm` snippet misfires on real names

The `§7` coverage-audit `sed` regex (`sed -E 's/^.*[."']//'`) mangles identifiers
like `byte_16_of_indices` / `ov_u32_of_nat` (drops leading `_`-joined segments).
The precise check: list `lemma_*` from `grep -hoE '^(noextract[[:space:]]+)?let( rec)? lemma_…|^fn lemma_…' src/*.fst`
and `lemma_*` from `grep -oE '_lemma_[a-zA-Z0-9_]+ = lemma_[a-zA-Z0-9_]+' test/*.Integration.fst`,
and require the two lists to be **identical**.  Two non-obvious anchors this
audit must include (missed once):

- **Pulse roundtrip `fn`s** (`lemma_pulse_*_roundtrip`) — they ARE lemmas despite
  being `fn`s, and need a `let _lemma_… = …` anchor like any `lemma_*`.
- **Pulse leaf `fn`s** (`encode_*`/`decode_*`) — anchor them too (`let _encode_uuid16 =
  encode_uuid16`), matching `fstar-basen`'s "mechanically protected against deletion" block.
  (`noextract` spec helpers and `type` decls stay unanchored, as they can't be value-
  anchored and are genuinely used by the `fn` bodies / `--custard_entry` roots.)

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

### Roundtrip lemmas are *easy* (unexpectedly)

Because the pure `codec` record's `.enc`/`.dec` are **computable projections**,
`dec (enc x)` reduces to `Inr (x, n)` and SMT discharges the roundtrip lemma
automatically — no `lemma_word32_shift_bytes`, no `h_mid` heap threading.  The
whole `lemma_low_roundtrip_*` family + `lemma_low_encode_decode_match` verify
with zero manual frame reasoning.

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

## 5. Common errors in the new surface

| Error | Meaning | Fix |
|---|---|---|
| 19 (timeout, word32 roundtrip) | low z3 rlimit | `--z3rlimit 120` |
| 317 | `--already_cached X` but cache lacks `X.fst.checked` | seed cache with stdlib `.checked` |
| 368 | `Prims.int` reached extraction | `noextract` the spec fn; `FStar.Int.Cast` in bodies |
| 134 / 285 | `Pulse` namespace not found | add the four `pulse/*` `--include` paths (or drop `--no_default_includes`) |
| 180 (`Unexpected operator **`) | `#lang-pulse` not active | load the Pulse lib (`open Pulse`); ensure `#lang-pulse` + Pulse includes |
| 10 | OCaml codegen batch of many files | one file per `--codegen OCaml` run |

## 6. Backend matrix (as verified this session)

| Backend | Mechanism | Status |
|---|---|---|
| `ocaml` | `--codegen OCaml` (legacy ML) | ✅ pure spec extracts (no Pulse needed) |
| `native` (C) | `--custard_backend C` (direct C11, no karamel) | ✅ Pulse leaf extracts + compiles |
| `fsharp` | `--codegen FSharp` / `--custard_backend FSharp` | 🟡 `.NET 10`, separate follow-up |
| `rust` | `--custard_backend KrmlRust` → karamel | ❌ dead upstream |
| `wasm` | — | ❌ gone (no backend) |

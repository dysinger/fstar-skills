---
name: fstar
description: F* language — index to sub-skills covering language, stdlib, proofs, Low*, and build.
---

# F\* (FStar) — Skill Index

F* is a dependently typed programming language combining SMT-based verification
with C/OCaml/WASM extraction.  This skill is split into focused sub-skills.

## Quick Reference

| I need to… | Read |
|---|---|
| Understand types, effects, operators, syntax | [fstar-lang](fstar-lang/SKILL.md) |
| Use Seq, List, Map, Set, Option | [fstar-stdlib](fstar-stdlib/SKILL.md) |
| Write lemmas, proofs, SMTPat, handle GADT barriers | [fstar-proofs](fstar-proofs/SKILL.md) |
| Debug codec combinator opacity, `.wfcv`/`.rest_cond` admits | [fstar-proofs §18](fstar-proofs/SKILL.md) |
| Audit cross-module buffer layouts (F* ↔ C) | [fstar-proofs §33](fstar-proofs/SKILL.md) |
| Audit admit()-bodied functions for buffer overflows | [fstar-proofs §34](fstar-proofs/SKILL.md) |
| Audit admit counts across docs/source (drift) | [fstar-proofs §40](fstar-proofs/SKILL.md) |
| Extract to C via KaRaMeL, Low* buffers | [fstar-lowstar](fstar-lowstar/SKILL.md) |
| Build, compile, nix derivations, OCaml extraction | [fstar-build](fstar-build/SKILL.md) |
| Write documentation, fsdoc comments, module headers | [fstar-docs](fstar-docs/SKILL.md) |

## Common Errors (by code)

| Error | See |
|---|---|
| 19 (subtyping, GADT type-refinement) | fstar-proofs §10 |
| 19 (opaque record field: codec .wfcv/.rest_cond) | fstar-proofs §18 |
| 47 (duplicate names, .fsti/.fst) | fstar-build § Module System |
| 53 (Ghost/Stack composition) | fstar-proofs §7 |
| 56 (bound variable escapes) | fstar-lowstar § Int.Cast Wrappers |
| 72 (identifier not found) | fstar-lang § Module System |
| 114 (pattern type mismatch) | fstar-lang § Match Syntax |
| 189 (C.Loops.while API) | fstar-lowstar § C.Loops |
| 233 (forward reference) | fstar-build § Module System |
| 308 (recursive dependency) | fstar-build § Module System |

## Keyword Collisions

| F* keyword | Safe name | See |
|---|---|---|
| `and`, `or`, `not` | `and_`, `or_`, `not_` | fstar-lang |
| `all`, `any`, `some`, `many` | `all_`, `any_`, `some_`, `many_` | fstar-lang |
| `fail`, `try`, `eof` | `fail_`, `try_`, `eof_` | fstar-lang |
| `type`, `match`, `let`, `in`, `if`, `then`, `else`, `fun`, `function` | Reserved — cannot use | fstar-lang |
| `module`, `open`, `val`, `rec`, `class`, `instance`, `effect` | Reserved — cannot use | fstar-lang |

## Module System

| Mechanism | Syntax | Transitive? |
|---|---|---|
| `open M` | Makes M's symbols available in current module | No |
| `include M` | Copy-pastes M's content; downstream sees symbols | Yes |

For re-exporters, use `include`.  For internal use, use `open`.
Full details: [fstar-lang](fstar-lang/SKILL.md) § Module System.

## Effect Hierarchy

```
PURE → Tot → DIV → EXN → ALL → ML
PURE → Tot → GHOST → GTot → STATE
```

- `Tot a` — total pure computation
- `GTot a` — total ghost (erased at extraction)
- `Lemma (requires pre) (ensures post)` — squashed proof (`Pure unit pre (fun _ -> post)`)
- `Stack` — Low* stateful, extractable to C

Full details: [fstar-lang](fstar-lang/SKILL.md) § Effect System.

## Syntax Quick Hits

- `a & b` is a tuple type; `(a, b)` is a tuple value
- `a * b` is a TUPLE TYPE (not multiplication). Open `FStar.Mul` for `*` as multiplication
- `a -> Tot b` is a total arrow
- `#a:Type` is an implicit argument (compiler infers)
- `{| d : hasEq a |}` is a typeclass dictionary (spaces required)
- `decreases` goes INSIDE the return type: `Tot b (decreases x)`
- Operators need spaces: `let ( >>= ) = ...` not `let (>>=) = ...`
- `noeq type` for records with function fields (skip decidable equality proof)

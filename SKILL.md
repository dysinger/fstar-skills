---
name: fstar
description: F* language — index to sub-skills covering the language, the stdlib, proofs, the build, and documentation, for the current F* toolchain (Custard/Pulse, Z3 5.3.0).
---

# F\* (FStar) — Skill Index

F* is a dependently typed programming language combining SMT-based verification
with extraction to OCaml and to C (via **Custard**, driven by **Pulse**).  These
skills describe **one** toolchain — the current F\* build:

| What | Today |
|---|---|
| Language surface | Custard + Pulse (`#lang-pulse`, `fn`, `pts_to`) |
| Stateful / C-extractable | Pulse — the only such language; `Pulse.Lib.*` (~81 modules under `ulib/pulse/lib/pulse/lib/`) |
| SMT solver | **Z3 5.3.0** — stricter than 4.13.3; a lost instantiation, not a lost budget |
| Multiplication | `a * b` **is** multiplication, no `open` (`FStar.Mul` does not exist) |
| Extraction | Custard: `--codegen Custard --custard_backend C` (or `OCaml`/`FSharp`) |

> ⚠️ **There is no reliable F\* auto-formatter.**  `--print`,
> `--print_in_place`, and the `--ide` `format` query all rewrite `(* *)`
> comments into invalid `//` comments and crash on `#lang-pulse` modules.  Leave
> `.fst`/`.fsti` hand-formatted (see [fstar-docs §11](fstar-docs/SKILL.md)).
>
> ⚠️ **Comment *layout* near SMT-fragile arithmetic lemmas is fragile.**  In one
> package, collapsing the fragmentary `(** *)` one-liners around
> `nbytes_of_varint`/`lemma_varint_*byte_arithmetic` into single blocks
> **correlated with** a non-terminating Pulse varint roundtrip hang (100% CPU
> z3).  The mechanism is unproven (SMTPat triggers are term-structural), so
> treat it as "re-verify after any edit there", not an immutable rule.  See
> [fstar-docs §13](fstar-docs/SKILL.md).

**Skills:** [fstar-lang](fstar-lang/SKILL.md) · [fstar-stdlib](fstar-stdlib/SKILL.md) ·
[fstar-proofs](fstar-proofs/SKILL.md) · [fstar-build](fstar-build/SKILL.md) ·
[fstar-docs](fstar-docs/SKILL.md)

## Quick Reference

| I need to… | Read |
|---|---|
| Extract to C with Custard/Pulse: the backend enum, the required flags, the C layout choices, the backend matrix | [fstar-build §15](fstar-build/SKILL.md) |
| Write a Pulse `fn` that extracts to clean C11: bounds in types, `Int.Cast` not `.v`, `noextract` specs | [fstar-build §16](fstar-build/SKILL.md) |
| Errors 317/368/134/285/180 in the Custard/Pulse surface | [fstar-build §17](fstar-build/SKILL.md) |
| A proof broke after a **Z3 bump** (5.3.x): `Failed to prove` or a *misleading* "timed out, increase the rlimit" — it is a LOST INSTANTIATION, not lost budget; name the fact, don't raise the limit | [fstar-proofs §116](fstar-proofs/SKILL.md) |
| A consumer flake now fails with `Function called without required argument "mimalloc-src"` | [fstar-build §14](fstar-build/SKILL.md) |
| Understand types, effects, operators, syntax | [fstar-lang](fstar-lang/SKILL.md) |
| Use Seq, List, Map, Set, Option | [fstar-stdlib](fstar-stdlib/SKILL.md) |
| `FStar.List.Tot` has no `take`/`drop`; `Seq.fold_left`/`Seq.count` are gone; `seq_to_list` head ≠ `index 0` | [fstar-stdlib §12–§14](fstar-stdlib/SKILL.md) |
| Write lemmas, proofs, SMTPat, handle GADT barriers | [fstar-proofs](fstar-proofs/SKILL.md) |
| **Z3 5.3.0** stops deriving a fact it used to find, and reports it as `Failed to prove` or a *misleading* "timed out, increase the rlimit" — the four measured diagnostics | [fstar-proofs §116](fstar-proofs/SKILL.md) |
| `decreases` with arithmetic fails to parse; `U8.t` is opaque (`v`/`v_inj`); `forall_intro_2` needs explicit `#p`; `assert_norm` will not reduce a `let` | [fstar-build §18](fstar-build/SKILL.md) |
| Reorder / split a proof-heavy module: `#push`/`#pop` unit extraction, tier closure, core vocabulary | [fstar-build §19](fstar-build/SKILL.md) |
| Make extracted repos uniform: byte-identical files, the deliverable set, unwrapped OCaml deps, local sibling flakes | [fstar-build §20](fstar-build/SKILL.md) |
| Debug codec combinator opacity, `.wfcv`/`.rest_cond` admits | [fstar-proofs §18](fstar-proofs/SKILL.md) |
| Make a `codec`-style record **bidirectional** (both laws); `remainder s` vs Lean's `Suffix n`; tautology trap | [fstar-proofs §87](fstar-proofs/SKILL.md) |
| A law that **fails in both `match` branches** — missing antecedent vs too-weak law | [fstar-proofs §88](fstar-proofs/SKILL.md) |
| Proof **needs rlimit 250+ and still fails** with all facts in context — suspect the *definition* (derive from an already-proved codec) | [fstar-proofs §89](fstar-proofs/SKILL.md) |
| Is a hypothesis **necessary**? Refute it with a law-abiding model; assert the failure in CI | [fstar-proofs §90](fstar-proofs/SKILL.md) |
| A **deletion test** went green suspiciously fast — three traps: the control asserts the hypothesis, a `let`-bound predicate won't unfold, or you blanked a lemma's **body** but kept its **statement** (the statement alone guides SMT) | [fstar-proofs §91](fstar-proofs/SKILL.md) |
| "Should this be a **record field or a parameter**?" — a value-dependent law cannot inhabit a field (elaboration error, not a proof failure); **forced ≠ useful**: also the vacuous and no-op-projection fold cases | [fstar-proofs §92](fstar-proofs/SKILL.md) |
| Changing a decoder's **return type** (count → remainder/slice) and the induction fails at the IH with `dec_result _ s` vs `dec_result _ (slice s …)` — a **dependency-width** failure, not arithmetic | [fstar-proofs §93](fstar-proofs/SKILL.md) |
| An **`exists` goal** that will not close with every fact in context — F\* introduces it itself **iff the witness is already NAMED**; `exists_intro` is needed only for a *computed* witness (fixed-width leaves need none) | [fstar-proofs §94](fstar-proofs/SKILL.md) |
| About to blame the **solver / toolchain / a numeric literal** — first look for a **counterexample to your own obligation** | [fstar-proofs §95](fstar-proofs/SKILL.md) |
| A **backward law** will not prove for a decoder — check whether `dec` accepts **non-image input** (overlong / alternate encodings); if so it is a design decision, not a proof | [fstar-proofs §96](fstar-proofs/SKILL.md) |
| Run that canonicality check as a **sweep over every leaf** — the cheap two-shape test, and why a per-field disposition table structurally cannot see the defect | [fstar-proofs §96](fstar-proofs/SKILL.md) |
| `open FStar.Mul` fails (`Error 134`) — `a * b` **is** multiplication now, so delete the `open`; the LSP tool historically disagreed with the runner in both directions | [fstar-proofs §98](fstar-proofs/SKILL.md) |
| Tempted to **weaken the law** so a permissive decoder fits? It is a dead end — the True/canonical dichotomy, and why `product`'s STEP kills it | [fstar-proofs §99](fstar-proofs/SKILL.md) |
| Proof over a **big-int encoder** is slow (100 s+) — stub lemmas, unsplit identity+range, or unrolled recursion | [fstar-proofs §97](fstar-proofs/SKILL.md) |
| **Route 1 of §93 worked end-to-end**: a decoder whose return type is indexed by its input, proven both ways — count decoder + refined accessor + one conversion | [fstar-proofs §93](fstar-proofs/SKILL.md) |
| **Split a module** safely: `make check` does not track deps; `include` ≠ `open`; unclosed `(** *` swallows a file; tier closure | [fstar-build §10b](fstar-build/SKILL.md) + [fstar-lang §2](fstar-lang/SKILL.md) + [fstar-docs §12](fstar-docs/SKILL.md) + [fstar-build §19](fstar-build/SKILL.md) |
| A **cross-repo parity gate** goes red after unrelated work — stash-test first; a check must compare the **shared** parts, not demand equality (a sibling's addition is not your regression) | [fstar-build §12](fstar-build/SKILL.md) |
| A **grep-based gate** (0 admits / rlimit) reports `clean` — check its file glob matches what you verify, and that its comment stripper is **nesting-aware** | [fstar-build §10](fstar-build/SKILL.md) |
| `make check` says **"Nothing to be done"** and exits 0 — force a real baseline with `OUT=/tmp/<fresh>`; it does not track dependencies | [fstar-build §10b](fstar-build/SKILL.md) |
| A published **lemma count** is wrong — `^let lemma_` misses **both** `let rec lemma_*` (31 in one library) **and** Pulse `fn lemma_*` (9); "every lemma is anchored" is a claim to check, not assume; a count without its command drifts | [fstar-build §11](fstar-build/SKILL.md) |
| **Moving the F* pin** across releases: the upstream tag itself may not build (z3 5.x inherited patch), every consumer must pass newly-required args (`mimalloc-src`), and the new default solver invalidates proofs in the fork *and* downstream — the gate is per-repo `nix build .#checked`, not `flake metadata` | [fstar-build §14](fstar-build/SKILL.md) |
| A **coverage sweep** reports "nothing missing" — re-run it with `^(let|let rec|fn) lemma_`; also: "used in `src/`" ≠ "anchored" (a lemma with no present consumer is caught *only* by its anchor), and never anchor dead code | [fstar-proofs §101](fstar-proofs/SKILL.md) |
| `forall_intro` fails with a bare `Error 19` — it does **not** discharge the lemma's `requires`; let SMT prove the `forall` directly. Also: a `let`-bound `prop` won't unfold into an argument, and `U8.uint_to_t` is `irreducible` (needs `vu_inv`) | [fstar-proofs §103](fstar-proofs/SKILL.md) |
| A proved roundtrip will not fit the law — check **which branch** the decoder takes at the *consumer's* budget; a side condition that is sometimes vacuous means **split the peel**, not add a hypothesis | [fstar-proofs §106](fstar-proofs/SKILL.md) |
| A `requires` you added so a wrapper would close — **suspect it is the counterexample's description**: if no proof consumes it and it restricts the input, test the excluded input (the empty one first) | [fstar-proofs §108](fstar-proofs/SKILL.md) |
| A lemma that was **true only because of a defect** — changing a decoder branch keeps every behavioural probe green and falsifies one offset-indexed lemma two files away | [fstar-proofs §111](fstar-proofs/SKILL.md) |
| A decoder guard now **reads an argument** (`i > 0`) — so every *equating* restatement is false at the stop; keep only the one-sided (`Inr`) form, and write the `index`/`slice` bridge lemma before the sequence lemma | [fstar-proofs §112](fstar-proofs/SKILL.md) |
| About to frame work as a **change of direction** — grep the decision record for the goal's own words; a goal in the basis of a decision is not new, and "open" in a ledger is not "abandoned" | [fstar-proofs §114](fstar-proofs/SKILL.md) |
| A decoder's `Inr (v, n)` is its **cursor, not a count** — so linking two decodes' counts (`n + i`) is false at every *stop*; test the linkage at the budget floor by evaluating both sides, and hold the refutation symbolic | [fstar-proofs §113](fstar-proofs/SKILL.md) |
| A locally re-declared `seq_of_list` **loses** the stdlib length refinement (restate it, delete your lemma); `match f a with` does **not** reduce under `f a = true` (split the base case per branch) | [fstar-proofs §109](fstar-proofs/SKILL.md) |
| About to present a **decision** — grep the spec first: if a requirement answers it, *apply* it and record the application; a menu whose options would weaken a `SHALL` is a re-litigation, not a choice | [fstar-proofs §110](fstar-proofs/SKILL.md) |
| The **core lemma is green and the wrapper is not** — suspect the **statement's exponent/indexing**, not the maths: prefer absolute indices over relative offsets in a recursive `ensures` | [fstar-proofs §107](fstar-proofs/SKILL.md) |
| A multi-lemma law will not compile together — key helpers on the **arguments**, not a `let`-bound local (`good` is a `prop` and won't unfold); state every `ensures` in one form; deletion-test by **neutralising a statement**, not just deleting a call | [fstar-proofs §105](fstar-proofs/SKILL.md) |
| A **proved** lemma is about to be reused — instantiate the consumer's `requires` at the caller's arguments first; a proved hypothesis is not necessarily the one needed, and `admit ()` bodies verify silently | [fstar-proofs §104](fstar-proofs/SKILL.md) |
| A doc claims something is **"structural" / "enforced" / "type-level"** — check the field it says is gone is gone, and that the new type is actually instantiated in `src/`; a `()` lemma body is not evidence of vacuity — and its **complement**: a `()` body can hide a `requires` no caller can satisfy (a `pow2` in a `requires` never reduces) | [fstar-proofs §100](fstar-proofs/SKILL.md) |
| Audit cross-module buffer layouts (F* ↔ C) | [fstar-proofs §33](fstar-proofs/SKILL.md) |
| Audit admit()-bodied functions for buffer overflows | [fstar-proofs §34](fstar-proofs/SKILL.md) |
| Audit admit counts across docs/source (drift) | [fstar-proofs §40](fstar-proofs/SKILL.md) |
| Build, compile, nix derivations, OCaml extraction, the F\* pin | [fstar-build](fstar-build/SKILL.md) |
| Write documentation, fsdoc comments, module headers | [fstar-docs](fstar-docs/SKILL.md) |
| Cite code locations in plans/notes — **never bare line numbers**; re-derive with an owner-aware scan, and **never trust a carried total** | [fstar-docs §10](fstar-docs/SKILL.md) |

## Common Errors (by code)

| Error | See |
|---|---|
| 19 (subtyping, GADT type-refinement) | fstar-proofs §10 |
| 19 (opaque record field: codec .wfcv/.rest_cond) | fstar-proofs §18 |
| 47 (duplicate names, .fsti/.fst) | fstar-lang §2 |
| 53 (Ghost/effectful composition) | fstar-proofs §7 |
| 56 (bound variable escapes) | fstar-proofs §12 (wrap in `inline_for_extraction Tot`) |
| 72 (identifier not found — usually a missing `open`, or a name only `include`d) | fstar-lang §2 |
| 114 (pattern type mismatch — GADT or-pattern binds different types) | fstar-proofs §12 |
| 189 (loop / `decreases` / bad `*`-as-multiply shape) | fstar-lang §15, fstar-build §18 |
| 233 (forward reference) | fstar-lang §2 (`val` in a `.fsti`; move the def earlier) |
| 308 (recursive dependency) | fstar-lang §2 |

## Keyword Collisions

| F* keyword | Safe name | See |
|---|---|---|
| `and`, `or`, `not` | `and_`, `or_`, `not_` | fstar-lang |
| `all`, `any`, `some`, `many` | `all_`, `any_`, `some_`, `many_` | fstar-lang |
| `fail`, `try`, `eof` | `fail_`, `try_`, `eof_` | fstar-lang |
| `type`, `match`, `let`, `in`, `if`, `then`, `else`, `fun`, `function` | Reserved — cannot use | fstar-lang |
| `module`, `open`, `val`, `rec`, `class`, `instance`, `effect` | Reserved — cannot use | fstar-lang |
| `label` (in `#lang-pulse` modules only) | Reserved Pulse keyword — can't be a combinator or record field | [fstar-build §16](fstar-build/SKILL.md) |

## Module System

| Mechanism | Syntax | Transitive? |
|---|---|---|
| `open M` | Makes M's symbols available in current module | No |
| `include M` | Copy-pastes M's content; downstream sees symbols | Yes |

For re-exporters, use `include`.  For internal use, use `open`.

> ⚠️ **A re-exporter needs *both*.**  `include M` lets *consumers* of your
> module see `M`'s symbols, but it does **not** put them in your own module's
> scope for your own later definitions.  A facade that `include`s `M` and then
> names one of `M`'s functions gets `Error 72` — at a *downstream* module,
> which misdiagnoses the problem.  Write `include M` **and** `open M`.
> (Found 2026-11-01 splitting `Data.Codec.Types`; see
> [fstar-lang §2](fstar-lang/SKILL.md).)
Full details: [fstar-lang](fstar-lang/SKILL.md) § Module System.

## Effect Hierarchy

```
PURE → Tot → DIV → EXN → ALL → ML
PURE → Tot → GHOST → GTot → STATE
```

- `Tot a` — total pure computation
- `GTot a` — total ghost (erased at extraction)
- `Lemma (requires pre) (ensures post)` — squashed proof (`Pure unit pre (fun _ -> post)`)
- **Pulse `fn`** — the stateful, C-extractable language (`#lang-pulse`), with
  `requires`/`ensures` over `pts_to` views.  It is a separate language surface,
  not an effect in the `Tot`/`GTot` hierarchy above.
  See [fstar-build §15–§16](fstar-build/SKILL.md).

Full details: [fstar-lang](fstar-lang/SKILL.md) § Effect System.

## Syntax Quick Hits

- `a & b` is a tuple type; `(a, b)` is a tuple value
- `a * b` **is multiplication** — no `open` needed (`FStar.Mul` does not exist)
- `a -> Tot b` is a total arrow
- `#a:Type` is an implicit argument (compiler infers)
- `{| d : hasEq a |}` is a typeclass dictionary (spaces required)
- `decreases` goes INSIDE the return type: `Tot b (decreases x)`
- Operators need spaces: `let ( >>= ) = ...` not `let (>>=) = ...`
- `noeq type` for records with function fields (skip decidable equality proof)

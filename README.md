# F* Skills

A collection of skills for the [F*](https://www.fstar-lang.org/) programming
language — a dependently typed language that combines SMT-based verification
with extraction to C, OCaml, and WASM.

These skills capture hard-won, verified experience: proof patterns, SMT
limitations, Low\* buffer patterns, KaRaMeL extraction gotchas, and build
recipes.  They are written to be reused by anyone writing or verifying F*
code.

## What's inside

| Skill | Covers |
|---|---|
| [`fstar-lang`](fstar-lang/SKILL.md) | Types, effects, operators, syntax, modules, typeclasses, tuples, termination |
| [`fstar-stdlib`](fstar-stdlib/SKILL.md) | `Seq`, `List`, `Map`, `Set`, `Option`, `Classical`, `Squash` |
| [`fstar-proofs`](fstar-proofs/SKILL.md) | Lemmas, SMTPat, induction, GADT barriers, Ghost/Stack bridging, proof errors |
| [`fstar-lowstar`](fstar-lowstar/SKILL.md) | Low\* buffers, KaRaMeL C extraction, `Int.Cast`, `C.Loops` |
| [`fstar-build`](fstar-build/SKILL.md) | Verification commands, nix derivations, OCaml extraction |
| [`fstar-docs`](fstar-docs/SKILL.md) | fsdoc comments, module headers, documentation standards |

Start at [`SKILL.md`](SKILL.md) for a quick-reference index (common errors,
keyword collisions, effect hierarchy), then open the sub-skill for your task.

## Installation

The `SKILL.md` + `skill.yaml` + `<name>/SKILL.md` layout follows the
`.pi/skills/` convention used by coding agents.  To install into an agent's
skill directory:

```bash
mkdir -p ~/.pi/skills/fstar
cp -R SKILL.md skill.yaml fstar-*/ ~/.pi/skills/fstar/
```

The files are plain Markdown, so they also read fine standalone — each
`SKILL.md` is a self-contained reference with cross-links to the others.

## License

[CC-BY-4.0](LICENSE).  You are free to share and adapt this material with
attribution.

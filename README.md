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

These skills follow the [Agent Skills](https://agentskills.io/specification)
format, so any agentic coding harness that supports it can load them.  You
clone the repo once, then point your harness's skill directory at it (via a
symlink) — the Git repo stays the single source of truth, and updates are a
`git pull`.

### 1. Clone the repo

```bash
git clone https://github.com/<you>/fstar-skills ~/repos/fstar-skills
```

### 2. Link it into your harness's skill directory

Symlink the cloned repo into the skill directory of each harness you use:

| Harness | Skill directory |
|---|---|
| Claude Code | `~/.claude/skills/` |
| OpenAI Codex | `~/.codex/skills/` |
| Cline | `~/.cline/skills/` |
| Pi | `~/.pi/agent/skills/` |

```bash
mkdir -p ~/.claude/skills
ln -s ~/repos/fstar-skills ~/.claude/skills/fstar
```

(Repeat the `ln -s` for each harness, replacing `~/.claude/skills` with the
other directories above.)

### 3. Update

```bash
cd ~/repos/fstar-skills && git pull
```

Because the symlink points at the cloned repo, a `git pull` is all it takes to
pick up changes — no re-copying.

The files are plain Markdown, so they also read standalone: each `SKILL.md` is
a self-contained reference with cross-links to the others.

## License

[CC-BY-4.0](LICENSE).  You are free to share and adapt this material with
attribution.

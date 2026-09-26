---
name: fstar-docs
description: F* documentation — fsdoc comment format, module headers, LSP hover docs, doc extraction, and documentation standards.
---

# F\* Documentation (fsdoc)

> Cross-reference: [fstar index](../SKILL.md).

F* uses `(** ... *)` doc comments, identical to OCaml's ocamldoc format.
These comments are parsed by the F* compiler, surfaced by LSP for hover
tooltips, and can be extracted for standalone documentation.

## 1. Doc Comment Syntax

```fstar
(** Brief one-line summary.

    Detailed description.  May span multiple paragraphs.

    @param name Description of the parameter
    @returns Description of the return value *)
let my_function (name: typ) : return_type = ...
```

### Rules

- `(**` opens a doc comment (double asterisk — NOT single `(*`)
- `*)` closes it
- First sentence is the brief summary (used in hover tooltips)
- Subsequent lines are detail prose
- `@param name description` documents a parameter
- `@returns description` documents the return value
- Blank line separates summary from detail

### What NOT to do

- Do NOT use `(* ... *)` for documentation — these are implementation comments, ignored by tooling
- Do NOT use `///` — while valid, it's inconsistent with `(**` and creates maintenance burden
- Do NOT put doc comments after the declaration — F* associates them with what follows

## 2. Module Headers

Every module SHALL start with a module-level doc comment:

```fstar
(**
<Module.Name> — One-line summary of the module's purpose.

Detailed description.  What abstractions it provides, how it relates
to other modules, what invariants it maintains.

@header Module.Name

@section SectionName
Description of grouped items under this section.
*)
module Module.Name
```

### Section headers

Within a module, group related items with section doc comments:

```fstar
(** Types *)

(** [codec a] — 8-field record ... *)
(** [error_code] — sum type ... *)

(** Combinators *)

(** Combinator 1: token — any single byte. *)
```

Use `(** Name *)` on a single line for section headers.
Use multi-line `(**` for item documentation.

## 3. What to Document

| Symbol type | Required | Tags |
|---|---|---|
| Module | Yes | `@header` |
| `type` / `noeq type` | Yes | Description of each constructor/field |
| `val` / `let` function | Yes | `@param` for each, `@returns` |
| Lemma | Yes | `@param`, description of `requires`/`ensures` |
| Combinator | Yes | Encoding/decoding behavior, wfcv semantics |
| Helper function | Yes | Purpose, parameters |
| `let rec` function | Yes | Termination measure description |

### Combinator documentation template

```fstar
(** Combinator N: name — one-line summary.

    @param p1 Description of first parameter.
    @param p2 Description of second parameter.
    Encodes as [...].  Decoder reads [...] bytes.
    wfcv: [...].  Fails with [ErrorCode] when [...].
    Built from [other_combinator] via [map_]. *)
let combinator_name (p1: typ1) (p2: typ2) : codec a = ...
```

## 4. LSP Integration

F* LSP surfaces `(**` doc comments as hover tooltips. When a user hovers
over a symbol, the LSP displays the doc comment from the symbol's definition.

This means:
- Doc comments on `let` bindings appear when hovering over uses of that binding
- Doc comments on `type` definitions appear when hovering over the type
- Module-level doc comments appear when hovering over the module name

The LSP reads doc comments at parse time — no special flag needed.

## 5. Doc Extraction

F* does not ship a standalone `--fsdoc` HTML generator. Doc comments can
be extracted with a Python script:

```python
import re

def extract_docs(fname):
    with open(fname) as f:
        content = f.read()
    for m in re.finditer(r'\(\*\*(.*?)\*\)', content, re.DOTALL):
        text = m.group(1).strip()
        # Parse @param, @returns, etc.
        ...
```

Extract `(** ... *)` blocks with `re.DOTALL` flag. Strip leading `*` from
continuation lines if present. Parse `@tags` with `re.findall`.

## 6. Documentation Standards

- Every public type, function, combinator, and lemma SHALL have a `(**` doc comment
- Module headers use `(**` with `@header` tag
- Section headers use `(** Name *)` format
- `@param` for each named parameter
- `@returns` for the return value
- All `///` comments SHALL be converted to `(**` format
- No undocumented `let` bindings in production code
- Use `(**` consistently — never mix `///` and `(**)` in the same file

## 7. Common Mistakes

| Mistake | Fix |
|---|---|
| `(* ... *)` for docs | Use `(** ... *)` |
| `///` comments | Convert to `(** ... *)` |
| Missing `@param` | Add one per parameter |
| Doc after declaration | Move doc before the `let`/`type` |
| `(*** Section ***)` | Use `(** Section *)` |
| Session-specific comments | Remove — docs are permanent |
| No module header | Add `(**` with `@header` |
| `(*)` inside `(**` doc comment | Reword to avoid `*)` sequence — "F star" — per fstar-proofs §36 |
| Lemma-count drift in doc headers | Run `grep -c '^let lemma_' file.fst` after add/remove; cross-check @header counts |
| Stale `@header` lemma counts in update tables | Keep module tables in sync with source header counts — same grep pattern |
| `#push-options` inside `(** ... *)` | Move directive BEFORE or AFTER the doc comment; `#push-options` inside a comment is dead code |
| Duplicate `(**` doc blocks | Keep only the doc immediately before the `let`/`type`; remove orphaned first block |
| Line starting with `module` inside fsdoc | Reword — `grep '^module '` in build loops AND Makefiles picks it up as a module name; causes phantom verify targets / wrong echo names. `head -1` then selects a prose line instead of the real `module X` declaration.
| Unclosed `(**` without matching `*)` | All subsequent source code (let bindings, types, lemmas, everything) is silently swallowed as doc-comment prose. No syntax error — just missing symbols (Error 72). Check `(**` / `*)` pairing anytime symbols vanish after doc edits. |

## 8. `(* *)` Regular Comment Premature Closure

F* does not nest comments of any kind.  The sequence `*)` ALWAYS closes
the innermost open comment, regardless of whether `(*` or `(**` opened it.

Consequence:
```fstar
(* star rparen — SQL count(*)  *)  ← the *) inside count(*) closes the comment!
```
The comment `(* count(*) *)` closes at the first `*)`, leaving `*)` as
unmatched source code.  This produces Syntax Error 168 at the line AFTER
the comment — confusing because the error message points one line past
the actual problem.

**Fix**: reword the comment to avoid `*)` inside `(* ... *)` or `(** ... *)`:
```fstar
(* star rparen — SQL count star close paren *)
```

This applies to BOTH regular comments `(* *)` and doc comments `(** *)`.
Error 168 at or near EOF with no obvious cause → search for `*)` inside comments.

## 9. Lemma Count Audit

Lemma counts in `@header`/coverage sections drift as lemmas are added and
removed.  The count in the doc comment is manual prose — F* does not
enforce it.

### Audit procedure

```bash
# Count actual lemmas in a file
grep -c '^let lemma_' file.fst

# Verify header count matches
grep 'Coverage audit\|compliance lemmas' file.fst
```

### Known drift patterns

- **Overshoot** (header > actual): phantom adds — the count was bumped but
  lemmas were never written, or lemmas were added then some removed without
  decrementing.  Example: header said 73 but `grep -c` showed 70.
- **Undershoot** (header < actual): stale after a batch add — lemmas were
  added but the header wasn't updated.

### Prevention

After ANY session that adds or removes lemmas:
1. `grep -c '^let lemma_' file.fst`
2. Update the doc comment header count
3. Update any derived status-table count in the same commit

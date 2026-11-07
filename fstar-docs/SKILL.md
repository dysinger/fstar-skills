---
name: fstar-docs
description: F* documentation — fsdoc comment format, module headers, LSP hover docs, doc extraction, and documentation standards.
---

# F\* Documentation (fsdoc)

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
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
| **Bare line numbers in plans/notes** (`Types.fst:1732`) | **Never do this.** They rot on the next insert/refactor and fail *silently* — the cited line still exists, just refers to something unrelated. Cite `file.fst: name_of_definition` instead; a name greps, a number cannot. If coordinates are unavoidable, record the commit they were true at. See §10. |

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

⚠️ **`grep -c '^let lemma_'` is NOT the lemma count.**  F\* has three
lemma-declaration forms and this pattern matches one of them:

| form | matched by `^let lemma_`? |
|---|---|
| `let lemma_*` | yes |
| `let rec lemma_*` | **no** |
| `fn lemma_*` (Pulse) | **no** |

A real audit (2026-11-07) reported 62 with this pattern, then 71 after adding
`^fn`, when the true total was **102** — 31 `let rec` lemmas were invisible.
Three successive "verified" numbers in prose.  Full recipe and the coverage-sweep
consequence: `fstar-proofs` §101.

```bash
# Count actual lemmas (all three forms; sort -u dedups mutual-rec / val+let pairs)
grep -rhoE '^(let|let rec|fn) lemma_[A-Za-z0-9_]+' src/*.fst \
  | sed -E 's/^(let rec|let|fn) //' | sort -u | wc -l

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
1. Re-run the three-form count above (not `grep -c '^let lemma_'`)
2. Update the doc comment header count
3. Update **every** derived count in the same commit — grep the whole repo for
   the old number.  A count typically appears in three places (the `@header`
   comment, a README table row, and a prose summary); fixing one and not the
   others is how "76" survives a correction to "71".

### A count must be published with its command

State the rule next to the number ("62 `let` + 31 `let rec` + 9 `fn`"), never a
bare total.  A bare total invites `grep -c '^let lemma_'`, which returns a
*smaller plausible number*, and the next reader concludes the doc is wrong and
"fixes" it to the wrong value.  That loop ran three times in one change.

## 10. Never carry bare line numbers in plans, notes, or task lists

Verified 2026-11-01: a task list cited 11 sites as bare line numbers
(`Types.fst:1732,1914,2108,…`).  **Every single one was wrong** — two edits had
landed since they were captured (a module split, and a new `type` inserted
~90 lines earlier).  What they pointed at:

| cited | actually was |
|---|---|
| `1732` | a comment ending `Definitional within this module. *)` |
| `1914` | `else let tag = Seq.index s 0 in` |
| `2108` | `\| Inr (tl, n2) -> Inr (v :: tl, n1 + n2)` |

The count was wrong too (26 sites, not 11; and 11 of those were trivial).

### Why this is worse than an ordinary stale doc

A stale *name* fails loudly — `Error 72`, identifier not found.  A stale *line
number* **always resolves to valid text**, so it looks correct.  A reader who
trusts it writes a confidently wrong table and has no signal that anything is
amiss.  Silent failure is the whole problem.

### The rule

- Cite `module.fst: name_of_thing`, never `module.fst: 1234`.
- If a coordinate is genuinely unavoidable, **record the commit** it was true
  at, and say so next to it.
- Treat any inherited list of line numbers as **suspect by default** and
  re-derive before using it.

### Re-derive with an owner-aware scan, not `grep -n`

`grep -n` gives you the line but not *what it belongs to* — which is what a
per-site verdict table actually needs:

```python
import re
src = open('Data.Codec.Types.fst').read().split('\n')

def owner(n):                      # nearest preceding top-level `let NAME`
    for i in range(n - 1, -1, -1):
        m = re.match(r'^let (?:rec )?([a-zA-Z_0-9]+)', src[i])
        if m:
            return m.group(1)

for n, line in enumerate(src, 1):
    if re.match(r'\s*rest_cond\s*=', line):        # or wfcv_prop, etc.
        print(owner(n), n, line.strip()[:60])
```

This yields `('product', 1874, 'rest_cond = (fun (v1, v2) r ->')` — a name
plus a bare-ish record field — and it also separates the *trivial* sites
(`fun _ _ -> True`) from the ones that need a real decision, which the line
list never did.

### ⚠️ The scan above still undercounts — field-pattern matching has TWO blind spots

Verified 2026-11-02, on the same file.  Running the scan above and trusting its
total gave **25 literals / 51 sites**.  The truth was **27 / 54**.  Two literals
were invisible, for two different reasons:

| blind spot | example | the pattern that misses it |
|---|---|---|
| The record literal does **not** open with `= {` on the declaration's own line | `let sum … =` … `in` … `  {` (a bare `{` on a body line) | any `= {$`-anchored scan, including an "owner" walk-back keyed to `= {` |
| The fields are **parameters**, not literal `field = …` lines | `custom` (`wfcv_prop_custom`, `rest_cond_custom` arrive as arguments) | any `^\s*wfcv_prop\s*=` scan |

**So a field-pattern scan is necessary but not sufficient.**  Count record
*literals* by a brace-depth scan keyed on **either** `= {` **or** a line whose
stripped content is exactly `{`, attribute each to the nearest preceding
top-level `let`, and exclude `type` declarations:

```python
import re
def literals(path):
    lines = open(path).read().split('\n')
    out = []
    for i, l in enumerate(lines):
        if l.rstrip().endswith('= {') or l.strip() == '{':
            for j in range(i, -1, -1):
                if re.match(r'^(let|type)\b', lines[j]):
                    if re.match(r'^let', lines[j]):
                        out.append((j, i, re.match(r'^let\s+([A-Za-z0-9_]+)', lines[j]).group(1)))
                    break
    return lines, out
```

Then assert the invariant that makes the total checkable: **each literal
carries exactly one `wfcv_prop` and one `rest_cond`**, so `sites == 2 ×
literals`.  If that fails, the scan is wrong — not the file.

### A carried TOTAL is not evidence either

The failure mode repeated one level up.  F29 says do not carry line numbers;
the same session produced **four different summary totals** (30/12/16/2/1,
27/11/14/1/0, 26/11/14/0/1, 27/11/14/0/1) from the *same* table, each by a
different reading, none by recomputing from source.  The tell that a total is
guessed rather than computed is **that it changes between drafts**.

- Recompute every total from source in the same command that writes it.
- Show the arithmetic, not just the result (`28 + 11 + 14 + 1 = 54`).
- State the reconciliation when rows and sites differ (`27 rows, 54 sites`).
- If a reader cannot reproduce the number from the artifact, the number is
  prose, not data.

### Withdraw a claim you cannot re-verify — in writing

Two claims made during that session were checked after being written and did not
hold (a fabricated span-attribution bug; an early tally).  Both were **removed
and the removal recorded**, rather than quietly edited out.  A research note
that only ever accretes findings cannot be trusted: a retraction is the signal
that the document is being checked.

---
name: fstar-build
description: F* build system — verification commands, nix derivations, OCaml extraction, passthru variants.
---

# F\* Build System

> **Version:** pinned to F\* ≤ 2025.12.15 (Low*/KaRaMeL era).
> For ≥ v2026.09.20 (Custard/Pulse, `krml`/Low* removed), see
> [`fstar-2026.09.20`](../fstar-2026.09.20/SKILL.md).
> Extracted from the full F* skill.  Cross-reference: [fstar index](../SKILL.md).

---

## 1. Verification Commands

```bash
# Single module
fstar.exe --cache_off --include ./src module.fst

# Multiple modules
fstar.exe --cache_off --include ./src --include ./base src/*.fst

# All modules in directory (loop)
for f in ./src/*.fst; do fstar.exe --cache_off --include ./src "$f"; done

# With Z3 resource limit increase
fstar.exe --z3rlimit 50 --cache_off --include ./src module.fst

# Interface file first, then implementation
fstar.exe --cache_off Module.fsti Module.fst
```

### Key Flags

| Flag | Purpose |
|---|---|
| `--cache_off` | Skip checked-file caching |
| `--cache_checked_modules` | Use checked files for already-verified modules |
| `--include DIR` | Add directory to include path |
| `--z3rlimit N` | Z3 resource limit (default 5, increase for proofs) |
| `--split_queries always` | Each branch = independent SMT query |
| `--admit_smt_queries true` | Admit SMT queries, keep type-checking |
| `--query_stats` | SMT query count per function |
| `--detail_errors` | Verbose error messages with context |
| `--detail_hint_replay` | Step-by-step hint replay log |

### `fstarArgs` vs `extractArgs`

- **fstarArgs** (verification): MUST include `--cache_checked_modules`
- **extractArgs** (code generation): MUST NOT include `--cache_checked_modules` (causes cross-module inlining error)

Both MUST include `${fstarUlib} --include ${fstarUlibChecked}`.

---

## 2. FSTAR_PATH Environment Variable

Custom F* supports colon-separated include paths via `FSTAR_PATH` (like `C_INCLUDE_PATH`):

```bash
export FSTAR_PATH="./src:../lib/src"
fstar.exe Module.fst  # no --include flags needed
```

---

## 3. Nix Derivation Pattern

```nix
{ stdenv, lib, fstar }:
let
  pname = "my-pkg";
  version = "0.1.0";
  sources = [ "My.Module.fst" ];
  fstarExe = "${fstar}/bin/fstar.exe";
  fstarUlib = "${fstar}/lib/fstar/ulib";
  fstarUlibChecked = "${fstar}/lib/fstar/ulib.checked";
  fstarLib = "${fstar}/lib/fstar/lib";
  kremlinInclude = "${fstar}/include/krml";
  krmlExe = "${fstar}/bin/krml";
  fstarArgs = "--include . --include ${fstarUlib} --include ${fstarUlibChecked} --cache_checked_modules";
  extractArgs = "--include . --include ${fstarUlib} --include ${fstarUlibChecked}";
in stdenv.mkDerivation {
  name = "${pname}-${version}";
  src = ./.;
  nativeBuildInputs = [ fstar ];
  buildPhase = ''
    for f in ${lib.concatStringsSep " " sources}; do
      ${fstarExe} ${fstarArgs} "$f" || exit 1
    done
  '';
  installPhase = "mkdir -p $out";
}
```

### krml-extraction loop `grep '\.Low\.'` silently matches ZERO modules

**Critical lesson**: a nix derivation's krml-extraction loop
derives Low\* module names by `grep '^module' src/*.fst`.
The filter MUST be `grep '\.Low'` (match the substring ".Low"), NOT
`grep '\.Low\.'` (match ".Low" followed by a literal dot).  A module named
`module Foo.Bar.Low` has NO trailing dot, so `grep '\.Low\.'` returns nothing,
the `for` loop iterates zero times, and the derivation **succeeds while
producing an empty artifact** (zero `.krml` files).

```bash
# Deterministic: the trailing-dot form matches nothing for a leaf Low module
echo 'module Foo.Bar.Low' | grep '\.Low\.'   # exit 1 (no match)
echo 'module Foo.Bar.Low' | grep '\.Low'      # matches
```

**Why it is invisible in the dev loop**: the `Makefile` uses the correct
`grep '\.Low'`, so `make krml` works; only the package's nix build exposes the
empty-artifact bug.  A `make check`-only workflow never catches it.

**Propagation risk**: this defect is COPY-PASTED across package `default.nix`
files, so one bad reference infects every downstream package that inherits the
pattern.  The correct `\\.Low` (or `\\.Low$`) is the reference form.

**Audit check**: `grep -rn "\.Low\." */default.nix` — every hit is a silent-empty
krml artifact and must be changed to `\.Low` (or `\.Low$`).

### `--cache_checked_modules` requires dependency-ordered verification (Warning 247)

**Critical lesson**: the auto-discovery `for f in src/*.fst` loop in
a `default.nix` iterates in **alphabetical** order.  When module `A` depends on
module `B` (via `open B` or `include B`) and `A` sorts before `B`, F* verifies `A`
first, cannot find `B.fst.checked` in `--cache_dir`, re-checks `B` *transitively*
(as a dependency — NOT written to `--odir`), and then emits **Warning 247** "checked
file `A.fst.checked` was not written" because a transitive dep's `.checked` was
missing.  The build still prints "All verification conditions discharged" and
succeeds, but the package's own `.checked` files are **silently incomplete** in
`$out` (e.g. a package ships only its `.Types` leaf, not the dependent module),
which then cascades to every downstream package that `open`s the missing module.

**Root cause**: with `--cache_checked_modules`, F* only writes the `.checked` for
the TOP-LEVEL target module, never for transitively-loaded dependencies.  The
closure must already be on disk in `--cache_dir`.  Pre-populating with
`cp ${fstar-checked}/*.checked $out/` covers the `ulib.checked` closure (files
incl. `.fsti.checked`), but NOT a package's own intra-package dependencies.

**The fix**: verify a package's modules in **dependency (topological) order** —
leaf modules (`.Types`, `.Chars`) first, dependent modules (those that `include`
a leaf) after:

```bash
# WRONG — alphabetical: the dependent module's .checked is never written
for f in src/*.fst; do fstar.exe $FLAGS --cache_checked_modules --cache_dir $out --odir $out "$f"; done

# RIGHT — leaf first, then dependents (Foo.Types before Foo)
$FSTAR $FLAGS --cache_checked_modules --cache_dir $out --odir $out src/Foo.Types.fst
$FSTAR $FLAGS --cache_checked_modules --cache_dir $out --odir $out src/Foo.fst
$FSTAR $FLAGS --cache_checked_modules --cache_dir $out --odir $out src/Foo.Low.fst
```

With `ulib.checked/*.checked` pre-populated, verifying the leaf then its dependent
writes both `.checked` files; the alphabetical loop writes only the first.  Each
package's `default.nix` must list its modules in dependency order.

**Reference shape** — an explicit dependency-ordered nix list (leaf modules FIRST,
keyed to `src/$mod.fst`):

```nix
# Nix list, leaf modules FIRST, keyed to src/$mod.fst
ordered-src-modules = [ "Foo.Types" "Foo" "Foo.Low" ];
# (in the derivation buildPhase)
for mod in ${builtins.concatStringsSep " " ordered-src-modules}; do
  ${fstar-exe} ${fstar-flags} --cache_checked_modules --cache_dir $out --odir $out \
    src/$mod.fst || exit 1
done
```

**Makefile trap — `$(sort ...)` is ALSO alphabetical**: a `Makefile` that builds
its `SRC_MODS`/`TST_MODS` with `| sort` has the exact same Warning-247 defect as
the nix glob (a dependent module sorts before its leaf and its `.checked` is never
written).  The `Makefile`'s per-module `out/checked/%.checked` pattern rule works
around it only by accident when GNU make resolves prerequisites in dependency
order; the explicit ordering fix (dependency-ordered lists) must be applied to
the `Makefile` too.

**Detection**: `ls <pkg>-checked` and confirm EVERY `module X` in `src/*.fst` has
`X.fst.checked` in `$out` (not just the alphabetically-first leaf).  A package with
`N` source modules shipping `< N` `.checked` files has this bug.

---

## 4. Passthru Variants (4 per Package)

| Passthru | Purpose | Output |
|---|---|---|
| `ocaml` | Source extraction | `.ml` files only |
| `opam` | Compiled OCaml | `.cmxa` + `META` in site-lib |
| `native` | C compilation | `.so` + `.h` (no `.krml`) |
| `wasm` | WASM compilation | `.wasm` |

### opam Passthru — META + site-lib

```nix
installPhase = ''
  local site_lib="$out/lib/ocaml/${ocaml.version}/site-lib/${pname}"
  mkdir -p "$site_lib"
  cat > "$site_lib/META" <<EOF
  name = "${pname}"
  version = "${version}"
  description = "..."
  requires = "fstar-runtime"
  archive(byte) = "${pname}.cma"
  archive(native) = "${pname}.cmxa"
  plugin(byte) = "${pname}.cma"
  plugin(native) = "${pname}.cmxs"
  EOF
  cp opam/* "$site_lib/"
'';
```

### native Passthru — No .krml in Output

The native passthru builds `.krml` intermediate files but only ships `.so` + `.h`:

```nix
installPhase = ''
  mkdir -p $out/lib $out/include
  cp krml/lib/* $out/lib/ 2>/dev/null || true
  cp krml/include/* $out/include/ 2>/dev/null || true
'';
```

---

## 5. Common Nix Errors

| Error | Cause | Fix |
|---|---|---|
| Error 134: Namespace not found | Missing `${fstarUlib}` in fstarArgs | Add both `ulib` and `ulib.checked` includes |
| Error 72: Identifier not found | Same as above | Same fix |
| Error 317: Cross-module inlining | `--cache_checked_modules` in extractArgs | Remove from extractArgs, keep in fstarArgs |
| drv.ocaml-src not parsed | `-` in attribute name | Use `drv."ocaml-src"` or rename to `ocaml`/`opam` |

---

## 6. OCaml Extraction & Demo Pipeline

### Two-Phase Extraction

```bash
# Phase 1: Check all modules (REQUIRED)
for f in Module1.fst Module2.fst Module3.fst; do
  fstar.exe $INC --cache_checked_modules "$f"
done

# Phase 2: Extract all modules to OCaml
for f in Module1.fst Module2.fst Module3.fst; do
  fstar.exe $INC --codegen OCaml --odir ocaml "$f"
done
```

### Compiling Extracted OCaml

```bash
FSTAR_LIB=/path/to/fstar/lib/fstar/lib
for f in *.ml; do
  ocamlopt -I . -I "$FSTAR_LIB" -c "$f"
done
```

### Linking Against F\* Runtime

```bash
FSTAR_PKG=/path/to/fstar/lib
export OCAMLPATH="$FSTAR_PKG:$OCAMLPATH"

ocamlfind ocamlopt -o demo \
  -I . -I "$FSTAR_LIB" \
  -package "fstar.lib" -linkpkg \
  Module1.cmx Module2.cmx driver.cmx
```

### F\* Runtime Transitive Dependencies

`fstar.lib` requires: `batteries`, `stdint`, `zarith`, `yojson`, `ppx_deriving_yojson.runtime`, `pprint`. All must be in `OCAMLPATH`.

### Build Order Matters

OCaml modules must be compiled in dependency order. Compile leaf modules before dependent modules. "Unbound module" errors mean reorder the compilation sequence.

---

---

### Multiple Pulse/Custard leaves — one root file + `--custard_entry` transitive close (verified fstar-image 2026-10-10)

A package with **multiple INDEPENDENT Pulse leaves** (e.g. `Data.Image.Pulse`,
`Data.Image.PNG.Pulse`, `Data.Image.QRCode.Pulse` — three enum-tag dispatchers
that do NOT `open`/`include` each other) cannot be extracted by listing all
three `.fst` files in ONE `--codegen Custard` invocation — `fstar.exe` fails with
**"Error 10: When using --ext fly_deps, only one file can be provided"**.  Nor can
you loop `for m in …; do … --odir $out src/$m.fst` — each iteration re-emits the
SAME `Custard.c`/`Custard.ml`/`Custard.fsproj` into `$out`, so only the LAST leaf
survives and the library silently drops the others (the `cc`/`dotnet build` still
succeeds on the partial `Custard.c` — a **silent-empty-artifact class bug**, same
family as the `grep '\.Low\.'` trap above).

**Correct pattern (single root file + entry flags, mirroring fstar-ip):**

```nix
# verify ALL leaves first (dependency order) so their .checked land in cache
for m in Data.Image.Pulse Data.Image.PNG.Pulse Data.Image.QRCode.Pulse; do
  ${fstar-exe} $PULSE_INCS --already_cached … --z3rlimit 120 \
    --cache_checked_modules --cache_dir cache --odir cache src/$m.fst || exit 1
done
# THEN one custard invocation rooted at ONE file, with ALL entry flags;
# the other leaves resolve from cache via --include cache.
${fstar-exe} $PULSE_INCS --include cache --already_cached … \
  --codegen Custard --custard_backend C --custard_monomorphize_types true \
  --custard_entry Data.Image.Pulse.encode_img_fmt \
  --custard_entry Data.Image.Pulse.decode_img_fmt \
  --custard_entry Data.Image.PNG.Pulse.encode_png_chunk \
  --custard_entry Data.Image.PNG.Pulse.decode_png_chunk \
  --custard_entry Data.Image.QRCode.Pulse.encode_qr_mode \
  --custard_entry Data.Image.QRCode.Pulse.decode_qr_mode \
  --odir $out src/Data.Image.Pulse.fst || exit 1
```

`--custard_entry M.f` pulls in the TRANSITIVE closure of `M` from the
`--include cache` `.checked` set, so the single root file links all three leaves
into one `Custard.c`.  The `#.checked`/`#.native`/`#.fsharp`/`#.ocaml` targets all
use this single-root form.

**OCaml `dune` module list must NOT include the Pulse leaves.**  Custard folds
all leaves into ONE `Custard` module (no per-leaf `Data_Image_Pulse.ml`), so:

```nix
ocaml-modules =
  (map (m: builtins.replaceStrings [ "." ] [ "_" ] m) pure-modules)  (* the --codegen OCaml leaves *)
  ++ [ "Data_Codec_Types"; "Data_Codec" ]  (* + the codec pure spec *);
# and the dune `(modules … Custard)` — Custard, NOT the pulse-modules.
```

Listing `Data_Image_Pulse`/`Data_Image_PNG_Pulse`/`Data_Image_QRCode_Pulse` in
`modules` fails dune with **"Module Data_Image_QRCode_Pulse doesn't exist"**
(only `Custard` is emitted).

### `make check` (dev loop) ≠ `nix build .#ocaml` — cross-module inlining is STRICTER

A lemma that discharges 0-admit under `make check`'s `--z3rlimit 120` can FAIL in
the `.#ocaml` derivation's `--codegen OCaml` pass (which uses cross-module
inlining — `--include cache` makes F* unfold callees from other modules).  The
ocaml-src `buildPhase` in `default.nix` verifies pure modules WITHOUT `--z3rlimit`
by default; a scanline/roundtrip lemma that SMT proved at rlimit 120 then fails
at the default rlimit.  **Fix: mirror `make check`'s `--z3rlimit 120` in the
pure-module verify loop of the `ocaml-src` buildPhase** (the native/fsharp loops
already carry it).

### `--codegen OCaml` requires dependency-order verification (Error 317)

`--codegen OCaml` with cross-module inlining fails with **"Error 317: Cross-module
inlining expects all modules to be checked first"** if the `pure-modules` list is
NOT in topological order — `open`-ing a module whose `.checked` was not yet written
(e.g. `Data.Image.QRCode.Render` listed BEFORE `Data.Image`).  `make check` may
pass with the mis-ordered list (F* auto-resolves transitively), but `--codegen
OCaml` is stricter.  Enumerate `pure-modules` (and `SRC_MODS` in the Makefile) in
EXACT dependency order, leaves first.

---

## 7. Profile-Guided Z3 Resource Limits
- Simple definitions: `--z3rlimit 40`
- Moderate proofs: `--z3rlimit 80-120`
- Complex proofs: `--z3rlimit 200-400`
- Very large GADT matches: `--z3rlimit 800` with `--split_queries always`

Start low and increase only when SMT fails. Use `--query_stats` to identify the function consuming the most resources.

---

## 8. File Path Conventions

### Flat Files

F* modules with dots in names use flat filenames, not directory trees:
```
src/Foo.Bar.Low.fst    # NOT src/Foo/Bar/Low.fst
```
Extraction commands must reference the flat path.

### out/ Directory

```
out/checked/  — .checked files
out/krml/     — .krml, .c, .h, .o
```

All gitignored.

---

## 9. LSP-Based Verification

The LSP approach (`fstar.exe --lsp` or an equivalent single-module checker)
typechecks a single F* module (no full `make` build needed). It resolves
project dependencies from the working directory and respect
`#push-options` / `#pop-options` directives for rlimits and tactic flags.

### Capabilities

- Proves lemmas, discharges SMT queries, verifies refinement types
- Resolves `open` / `include` from the project tree (not just F* stdlib)
- Same Z3 backend as `fstar.exe`

### Limitations

- One module at a time; no cross-module caching
- No `--cache_checked_modules` support
- Does NOT run the KaRaMeL extraction pipeline
- **Filename mismatch**: a checker that writes code to a temp file requires
the module name to match the temp filename (e.g. `Fails.fst` / module `Fails`)
OR be resolvable via the include path.  Source modules in `src/` work because
they are found via the include path; test modules in `test/` may fail if
`test/` is not in the include path.

### When to use

- Quick verification of single modules during development
- Testing lemma changes without a full `make check`
- Auditing proof coverage (paste key functions and test them)

Use the LSP check for individual-module verification; use a full build only for
final tree-wide verification.

### `fstar.exe --lsp` and `--ide` (editor integration)

`fstar.exe` ships TWO interactive modes for IDEs:

- `--lsp` — the native Language Server Protocol server (the modern target for
  VS Code / Kakoune / etc.).
- `--ide` — the OLDER JSON-based interactive protocol (pre-LSP).  Do NOT target
  it for new editor work; `--lsp` is the supported route.

There is no official F\* VS Code extension in a typical package registry.  A
VS Code setup must either (a) vendor an extension, or (b) register a minimal
local language-client extension whose `command` is `fstar.exe --lsp` over stdio.

**⚠ The editor LSP is a dev-loop aid, NOT the verification gate.**  `--lsp`
typechecking is LOOSER than `fstar.exe --z3rlimit 80` (see fstar-proofs §47/§52:
"LSP is looser than nix").  Editor diagnostics/hover are convenient, but the
full build with a Z3 resource limit is the source of truth.

## 10. Grep-based gates in a spike/test runner: two ways they silently do nothing

Verified 2026-11-07 on a spike runner whose job is to prove "0 admits, no
resource-limit escape" across a directory of evidence modules.  **Both bugs
below made the gate report `clean` while checking the wrong files.**  A gate
that never fires is worse than no gate: it certifies.

### Bug 1 — the file glob does not match the files you check

The runner verified modules by an explicit list but gated with a glob:

```bash
fstar.exe ... ModuleA.fst ModuleB.fst   # verified: listed explicitly
grep -nE 'admit' "$here"/spike-*.fst    # gated:   only names starting "spike-"
```

Every evidence module not named `spike-*` (route probes, counterexample
modules, sweep modules, refutation modules) was **outside the gate**.  An
`admit` — or a `#push-options --z3rlimit 900` — added to any of them would
have passed.

**Rule:** derive the gate's file list from the SAME variable the verification
loop consumes, never from a second pattern:

```bash
verified_srcs=()
for entry in $mods $refutations; do verified_srcs+=("$here/${entry%%:*}"); done
grep -nE 'admit' "${verified_srcs[@]}"
```

Then the two cannot drift.  A grep glob is a *second* definition of "the set
of files", and two definitions drift.

### Bug 2 — a non-greedy comment stripper closes at an INNER `*)`

To avoid flagging the *word* `admit` in prose, the gate stripped comments
with `re.sub(r'\(\*.*?\*\)', '', src, flags=re.S)`.  F\* comments **nest**,
and an inline `(* ... *)` inside a header block:

```
(* ===========================================================================
   ... if b < 128 then Inr (v', p + 1)      (* terminate at a final group *)
   ...
   No admit, no assume val, no #push-options over 400.
   =========================================================================== *)
```

makes the non-greedy regex stop at the **inner** `*)`.  Everything after it in
the header is then scanned as **code**, and the prose line
`No admit, no assume val, ...` is reported as a finding.  The fix for the
comment stripper is a depth counter, not a cleverer regex:

```python
def strip_comments(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if s.startswith('(*', i):        depth += 1; i += 2; continue
        if depth and s.startswith('*)', i): depth -= 1; i += 2; continue
        if depth:
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('//', i):
            k = s.find('\n', i)
            if k < 0: break
            i = k; continue
        out.append(s[i]); i += 1
    return ''.join(out)
```

Keep line structure (emit `\n` for comments' newlines) so reported line
numbers stay true.

### Always prove the gate both ways

A gate is only evidence if you have watched it **fire**.  Test it directly:

```bash
printf 'module T\nlet f () : Tot int = admit ()\n'  > /tmp/p1.fst   # expect exit 1
printf 'module T\n(* nested (* admit *) *)\nlet f () : Tot int = 1\n' > /tmp/p2.fst  # expect exit 0
```

If the first exits 0 the regex is wrong; if the second exits 1 the stripper is
wrong.  Both directions, every time the checker is edited.

## 11. Counts in a proof library: four ways a lemma total is wrong

Verified 2026-11-07 while auditing a library whose README said "67 lemmas,
mechanically anchored".  All of these errors were present **at once**, and each
alone was enough to make the number unusable.  The same audit then repeated
error 1 **twice more** while "fixing" it — 67 → 76 → 71, all wrong; the true
total was **102**.  That progression is the lesson.

### Error 1 — counting `^let lemma_` misses BOTH `let rec` and Pulse's `fn`

F\* has three lemma-declaration forms, and the intuitive grep matches one:

| form | counted by `^let lemma_`? |
|---|---|
| `let lemma_*` | yes |
| `let rec lemma_*` | **no** |
| `fn lemma_*` (Pulse) | **no** |

In the audited library: 62 `let` + **31 `let rec`** + **9 `fn`** = **102**.  The
`^let` grep said 62; adding `^fn` said 71; both were published as fact.
The 9 omitted `fn` lemmas were exactly the C-path roundtrip theorems — the ones
whose *absence* would matter most — and the 31 recursive lemmas were the
induction results behind the hardest proofs.

**Rule.** Count all three forms, dedup names:

```bash
grep -rhoE '^(let|let rec|fn) lemma_[A-Za-z0-9_]+' src/*.fst \
  | sed -E 's/^(let rec|let|fn) //' | sort -u | wc -l
```

`sort -u` matters: a `val` + `let` pair or a mutual-rec group repeats a name, so
a raw line count over-reports — the *other* silent error.  State the per-form
split in the document, because the next reader will run the `let` grep, get a
smaller number, and "fix" the doc to the wrong value.  Full story:
`fstar-proofs` §101.

### Error 2 — "mechanically anchored" is a claim, not a vibe

The library had a `Data.Codec.Test.Integration` module described as binding
every lemma so deletion breaks the build.  It bound **58 of 67**.  The other
nine could be deleted with a green build — and five of those nine were
referenced *nowhere*, i.e. dead code the coverage claim was hiding.

**Rule.** To check an anchoring claim, extract every lemma name — **all three
forms, same blind spot as error 1** — and require it to appear in the
integration module:

```bash
grep -rhoE '^(let|let rec|fn) lemma_[A-Za-z0-9_]+' src/*.fst \
  | sed -E 's/^(let rec|let|fn) //' | sort -u \
  | while read l; do
      grep -qE "(^|[^A-Za-z0-9_])$l([^A-Za-z0-9_]|$)" test/*Integration.fst \
        || echo "MISSING $l"
    done
```

Any `missing` entry falsifies "every lemma is anchored".  A sweep built on
`^let` alone reported **full coverage** while 4 `let rec` lemmas were in fact
unanchored — so re-run with the three-form pattern before believing a
"nothing missing" result.

Then decide per lemma: **anchor it** (if `src/` uses it) or **delete it** (if
nothing does).  Do not anchor dead code — an anchor for an unused lemma makes
deletion harder, which is backwards.

> BSD/macOS `grep` has **no `\b`**.  `grep -c "\b$name\b"` silently returns 0
> for every name, so a sweep written that way reports *everything* missing — a
> broken sweep that looks like a disastrous finding.  Use
> `-E "(^|[^A-Za-z0-9_])$name([^A-Za-z0-9_]|$)"`.

### Error 3 — a count without its command drifts, and the drift is invisible

The same README had earlier said 93 lemmas (truth 67) and "93 `Seq` lemmas"
when `FStar.Seq.Base` + `FStar.Seq.Properties` export **145** `val`s.  Both
numbers were plausible; neither was reproducible.

**Rule.** A published count carries the command that produces it, or a rule
precise enough to be machine-checked.  "102 lemmas (62 `let` + 31 `let rec` + 9
`fn`)" survives a re-audit; "93 lemmas" does not — and neither did "67", "76"
or "71", each of which was written down as verified.

**Corollary: grep the whole repo for the old number when you change it.**  A
count typically lives in three places (a doc comment, a README table row, a
prose summary).  Fixing one and not the others is how a stale total outlives
its correction.

### The audit lesson under all three

A count is a **claim about the code**, not a fact about the document.  Every
one of these was a number that had been copied forward through edits without
being re-derived.  Re-derive from source before publishing, and show the
arithmetic.

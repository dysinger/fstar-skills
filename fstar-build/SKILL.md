---
name: fstar-build
description: F* build system — verification commands, Custard/Pulse C extraction, nix derivations, OCaml extraction, passthru variants, the F* pin.
---

# F\* Build System

> **Toolchain:** F\* latest — Custard/Pulse, Z3 5.3.0, no KaRaMeL/Low\*.
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

### An extraction loop with a too-specific filter silently emits ZERO modules

**The defect class, still live.**  Any derivation that *derives its module list*
by filtering `grep '^module' src/*.fst` with a too-specific pattern silently
produces an empty artifact.  The canonical instance: filtering for leaf modules
with `grep '\.Low\.'` (match ".Low" followed by a literal dot) misses
`module Foo.Bar.Low`, which has no trailing dot — so the `for` loop iterates
zero times and the derivation **succeeds while producing nothing**.

```bash
# Deterministic: the trailing-dot form matches nothing for a leaf module
echo 'module Foo.Bar.Low' | grep '\.Low\.'   # exit 1 (no match)
echo 'module Foo.Bar.Low' | grep '\.Low'      # matches
```

**Why it is invisible in the dev loop**: the `Makefile` uses the correct
`grep '\.Low'`, so the extract target works; only the package's nix build
exposes the empty-artifact bug.  A `make check`-only workflow never catches it.

**Propagation risk**: this defect is COPY-PASTED across package `default.nix`
files, so one bad reference infects every downstream package that inherits the
pattern.  Use `\.Low$` (anchored), not `\.Low\.`.

**Audit check**: `grep -rn "\.Low\." */default.nix` — every hit is a silent-empty
artifact and must be changed to `\.Low$`.

**Generalisation (the durable rule):** grep-based gates and loops fail silently
in *both* directions — a filter that matches nothing and a filter that matches
too much both look like success.  Fix the **denominator first**, and assert it
(§10 Bug 1).

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
| `native` | C compilation (Custard) | `.so` + `.h` |
| `fsharp` | `.NET` compilation (Custard `FSharp`) | `.fsproj` + source |

There is **no `wasm` backend** — Custard's `--custard_backend` enum has no wasm
target (§15).

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

### native Passthru — C11 from Custard

The native passthru extracts with `--codegen C --custard_backend C` and
ships the compiled library plus the header (§15 for the flags, and for the
"one root file + `--custard_entry`" pattern when a package has several Pulse
leaves):

```nix
installPhase = ''
  mkdir -p $out/lib $out/include
  cp $out/lib/lib*.so $out/lib/lib*.a 2>/dev/null || true
  cp $out/include/*.h 2>/dev/null || true
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
three `.fst` files in ONE `--codegen C` invocation — `fstar.exe` fails with
**"Error 10: When using --ext fly_deps, only one file can be provided"**.  Nor can
you loop `for m in …; do … --odir $out src/$m.fst` — each iteration re-emits the
SAME `Custard.c`/`Custard.ml`/`Custard.fsproj` into `$out`, so only the LAST leaf
survives and the library silently drops the others (the `cc`/`dotnet build` still
succeeds on the partial `Custard.c` — a **silent-empty-artifact class bug**, same
family as the too-specific grep trap in §3).

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
  --codegen C --custard_backend C --custard_monomorphize_types true \
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
out/custard/  — .c, .h (Custard), and per-backend sources
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
- Does NOT run the Custard extraction pipeline (no codegen at all)
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

### Bug 3 — evidence that is IN the repo but not in the LIST

A related, later failure (2026-11-07, one change later): a directory of
evidence modules was rescued from `/tmp` into the repository — and still never
added to the runner's `mods` list.  The file glob would have caught them; the
explicit list did not.  So the fix for Bug 1 (derive from the list) does
**not** protect against forgetting the list.

**Rule:** after adding evidence files, assert the *count*, not just exit 0:

```bash
ls evidence/*.fst | wc -l                   # 10
grep -c ':' <<< "$mods"                     # must match (+ refutations)
```

Forgetting to add a file is invisible to a green run — the run is green
*precisely because* it was never checked.  A count assertion is the only check
that notices an omission.

And name the runner entry by the file's **declared module name**.  The runner
copies each file to its declared name before verifying, so a convenient alias
(`DIGITS_PEEL.fst:F42_DigitsPeel`) leaves the copy named `F42_DigitsPeel.fst`
while the file says `module DIGITS_PEEL` — `Error 141, Interactive mode only
supports a single module at the top-level`.  The error reads like a harness
problem and is really a one-line mismatch; check the module header.

### Always prove the gate both ways

A gate is only evidence if you have watched it **fire**.  Test it directly:

```bash
printf 'module T\nlet f () : Tot int = admit ()\n'  > /tmp/p1.fst   # expect exit 1
printf 'module T\n(* nested (* admit *) *)\nlet f () : Tot int = 1\n' > /tmp/p2.fst  # expect exit 0
```

If the first exits 0 the regex is wrong; if the second exits 1 the stripper is
wrong.  Both directions, every time the checker is edited.

## 10b. `make check` says "Nothing to be done" and you believe it

Verified 2026-11-09.  A `make`-driven verify target is **stamp-based**, so an
edit that does not touch a rule's prerequisites — or any edit at all, once the
stamp exists — reports

```
make: Nothing to be done for 'check'.
```

and exits **0**.  Read as a green baseline, that is the previous session's
result.  It bites hardest exactly when you need the baseline most: *before*
editing a core module, to know what you are breaking.

**Rule: force a real baseline by pointing the output dir somewhere fresh.**

```bash
make check OUT=/tmp/<unique-dir>       # first run: everything re-verifies
rm -rf /tmp/<unique-dir>               # if you want to re-run the same dir
```

Two traps around this:

- **The first `OUT=` run can pass while the second reports fully cached**, so
  read the `=== <Module> ===` lines of a *clean* run to know the real set, not
  the exit code of a cached one.  Grep for them:
  `make check OUT=/tmp/x | grep -E '^=== |Verified module|Error'`.
- **`make check` does not track dependencies.**  A changed `Types.fst` does not
  force `Pulse` or the test modules to re-verify, so "7 modules green" after a
  core edit can mean "one module green, six stamps reused".  A fresh `OUT=`
  removes the doubt.

This is the verify-side twin of §10's grep-side bug: both are gates that
*report clean without having looked*.

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

---

## 12. A cross-repo parity gate must compare the SHARED parts, not demand equality

Verified 2026-11-08.  The failure mode is the mirror of §10: there the gate
checked the wrong *files*; here it checks the right files with a relation that
is too strong, so an **unrelated change in the sibling repo turns this repo's
build red**.

### The case

`fstar-codec/check-readme-parity.sh` asserts that this repo's README and
`../lean-codec/README.md` have the **same list** of `##` headings — it diffs
the two lists and fails on any difference.  That held for months.  Then
`lean-codec` added a ninth section (`## The gate that keeps the gates honest`,
describing `Axioms.lean`/`lake build`) and this repo went red:

```
FAIL: the eight ## headings do not match ../lean-codec/README.md in name/order
  -## The gate that keeps the gates honest
```

**Nothing here was wrong.**  The local README still had exactly the eight
expected sections.  The check was asking "are these two documents identical in
structure?", which is not the property it documents ("the eight **shared**
sections agree in name and order").

### Why it matters more than a broken build

- **It misattributes blame.**  A red gate in the middle of unrelated work reads
  as "I broke something", and the cheap fix is to *edit the local README to
  appease the check* — which is the gate dictating content.
- **It cannot be satisfied.**  The Lean section describes an artifact with no
  F* analogue, so equality is unachievable, not merely inconvenient.
- **Stash-test before believing a red gate is yours.**  `git stash -u`, re-run,
  `git stash pop`.  Ten seconds, and it distinguishes "my regression" from
  "the sibling moved" — the same discipline as §95's "look for a
  counterexample to your own obligation" applied to build state.

### The rule

State the relation the check *claims* and implement exactly that:

```bash
# WRONG  — any sibling addition breaks us
diff <(headings ours) <(headings theirs)

# RIGHT  — we own these names and this order; additions elsewhere are theirs
for h in "${expected[@]}"; do check ours contains h, in order; done
```

and have the check **print what it skipped**, so a genuinely missing shared
section is still caught.  A parity check that cannot say "extra section in the
sibling, ignored" forces reviewers to guess.

**Not fixed at the time** (it needs its own change plus a mutation test, per
§10's rule 3 that a new check must be mutation-tested).  Recorded in
`codec-strict-isomorphism/research.md` F57 so the next session does not read
it as a regression.

| what | where |
|---|---|
| the check | `fstar-codec/check-readme-parity.sh` |
| the record | `codec-strict-isomorphism/research.md` F57 |

## 13. Verifying ONE module by hand: the four flags, and the three ways it silently misleads

Verified 2026-11-09 (`fstar-codec`).  Needed whenever you verify a scratch
module or one file without `make check`.

### The command that works

```bash
work=$(mktemp -d); mkdir -p "$work/out"
cp "$FSTAR_CHECKED"/*.checked "$work/out/" 2>/dev/null        # (2) below
UIDIR="$(fstar.exe --locate_lib)/ulib"
fstar.exe --no_default_includes --include "$UIDIR" \
  --include "$REPO/src" --include "$REPO/test" \
  --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore' \
  --z3rlimit 120 --cache_checked_modules --cache_dir "$work/out" --odir "$work/out" \
  "$work/Mod.fst"
```

### The three traps

1. **`Error 141: Interactive mode only supports a single module. Expected
   module X`** — the *filename* must equal the module name.  Spike files whose
   names do not match (`spike-alt.fst` declaring `module AltA5`) must be **copied
   into a scratch dir under the module name** first.  That is why spike runners
   carry a `file:Module` table.
2. **`Error 317: Expected Prims to be already checked`** — you must seed
   `--cache_dir` from `$FSTAR_CHECKED` (the devShell's pre-verified stdlib).
   Without the seed, `--already_cached` has nothing to find and every run
   re-checks `Prims`.
3. **`Warning 241: Unable to load ... does not exist; will recheck`** — expected
   on a fresh scratch dir; it is noise, not a failure.  Do not "fix" it by
   dropping `--already_cached`.

### F\* comment nesting bites the shell pipeline

`(\*` opens a comment, and a stray `*)` in prose **closes the file's header
early**.  In this session, writing an inline `(\* ... *)` inside an already-open
doc comment produced `Error 168: unexpected char` three times.  Rules:

- never write `(\*` inside a comment; use plain prose;
- if you edit comments with `python3`/`sed`, prefer removing the comment over
  escaping it;
- a `*)` in the *prose* of a header ends the doc comment, so every later
  declaration becomes "top-level code" and errors look unrelated.

### A file that verifies is the only evidence; a file that parses is not

Several iterations this session ended with "Verified module" printed *and* an
error, because the last declaration failed but earlier ones succeeded.  **Grep
for both `Verified module` and `Error` and read the exit code** — `=== exit=$? ===`
on its own line is the only reliable witness.

## 14. Moving the F* pin across releases: the three things that break downstream

Verified 2026-11-16 moving 13 consumer flakes `v2026.09.20+lsp` →
`v2026.10.25+lsp` → `v2026.11.15+lsp`.  The version bump itself is a one-line
edit; these are what actually fails.

### 1. The upstream tag may not build at all — check before blaming your fork

`v2026.10.25` and `v2026.11.15` **were unbuildable** as first pinned (the
current pin fixes this), for a reason unrelated to any local change:

```
building z3-5.3.0
  applying patch .../fix-pkg-config-paths.patch
  Hunk #1 FAILED at 1.
```

nixpkgs packages z3 **5.1.x**, and its `fix-pkg-config-paths.patch` rewrites
5.1.x's `z3.pc.cmake.in`.  `.nix/z3_5_3_0.nix` does `z3.overrideAttrs`, so it
inherits that patch and applies it to **5.3.0** source, where the hunk no longer
matches.  5.3.0 still has the *bug* the patch fixed (`${exec_prefix}/` prefixed
onto an absolute `@CMAKE_INSTALL_LIBDIR@` yields `${exec_prefix}//nix/store/…`,
which the pkg-config fixup rejects), so the correct repair is a **new patch
written against 5.3.0's template** and `patches = [ ./my.patch ];` — not
`patches = [ ]`, which fails later in `fixupPhase` with
`Broken paths found in a .pc file!`.

> **Diagnose bottom-up.** Build `.#z3` first, then `.#` — a z3 failure wears
> the same "Cannot build …/fstar-…drv" shape as an F* failure.

### 2. Every consumer must now pass the arguments `fstar.nix` gained

`v2026.11.15` added a required `mimalloc-src` (it copies the source into
`ulib/c/mimalloc` for the Cherry C backend) — *historical*, and stated as an
example.  The *current* argument list is whatever the pin's `fstar.nix` takes:
re-read it rather than copying this one.  Every flake that
`callPackage`s `.nix/fstar.nix` directly must supply it, or **evaluation**
aborts:

```
Function called without required argument "mimalloc-src" at .nix/fstar.nix:11
```

The fix pattern, per consumer flake:

```nix
mimalloc-src = { url = "github:microsoft/mimalloc/v3.6.1"; flake = false; };
# ...
fstar = (ocamlPackages.callPackage (inputs.fstar + "/.nix/fstar.nix") {
  inherit version z3;
  inherit (inputs) mimalloc-src;   # <-- required by the current fstar.nix
  ocamlLibraryPath = "";
});
```

Pin the **same tag the fstar flake itself pins**, so the two cannot drift.

The pin the fork carries is only the `+lsp` suffix — the *language and
toolchain* surface is upstream F\* latest, so the arguments `.nix/fstar.nix`
requires track upstream's own build.  When you move the pin, re-read the
argument list **once** and mirror it in every consumer; a missing argument is
an evaluation error, not a build error, so `nix flake metadata` will not see
it.

> **Do not replace the `buildPhase`.**  Patching a derivation's `buildPhase`
> with your own means every later upstream change to it is silently dropped.
> Pass the new argument and stop there.

### 3. A new default solver invalidates proofs, in the fork AND in the consumer

F* made Z3 5.3.0 the default in `v2026.10.25`, and it is stricter.  Two
consequences:

- **Upstream's own `ulib`/pulse may not verify.**  `ulib/FStar.Int.fst`'s
  `ones_to_vec_lemma = ()` had to be repaired by hand; see
  [fstar-proofs §116](../fstar-proofs/SKILL.md) for the mechanism and the
  "name the fact, don't raise the limit" rule.
- **Downstream repos break independently.** Moving `fstar-image` needed two
  outer fixes (one rlimit, one 36-minute *hang* turned into <3 min by asserting
  two `%` bounds per step).

So a pin bump is **not done when the flake evaluates.** The gate is:

```bash
for d in <repos>; do (cd $d && nix build .#checked --no-link) ; done
```

and each `-checked` must actually run.  Expect to repair proofs in proportion
to the repo's size; do not report "migrated" from `nix flake metadata`.

### Corollary: the pin is a fork — it carries the LSP server, not a version

The `fstar` flake input points at the `dysinger/fstar` fork, whose only
difference from upstream is that it **carries the LSP server** (upstream does
not ship one).  The tag suffix says exactly that — `+lsp` — and the base is
whatever upstream release the fork currently tracks, i.e. **the latest**.  Read
the pin out of the flake (`inputs.fstar.url`) rather than hardcoding it.

When the upstream base moves, the fork must be rebuilt: cherry-pick the LSP
commit onto the new upstream tag and resolve the conflicts that upstream's own
progress creates (they recur in `FStarC.Errors.Codes` — upstream keeps claiming
new error codes; the LSP errors just move up), then re-tag and re-push.  Always
verify the new tag resolves before re-pinning consumers:

```bash
nix flake metadata "github:dysinger/fstar/<the pin's tag>"   # before touching consumers
```

---

## 15. Custard: the only C-extraction path, and Pulse: the only stateful language

F\* latest ships **Custard**, a whole-program, demand-driven, monomorphizing
extractor whose C backend emits direct C11 with **no runtime glue**, and
**Pulse** (`#lang-pulse`, `fn`, `pts_to`) as the stateful language that Custard
understands.  There is no other route to C.

```fstar
module Data.Codec.Pulse
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

### The Pulse stdlib ships inside the install

Under `$(fstar.exe --locate_lib)/pulse` (~81 modules under
`ulib/pulse/lib/pulse/lib/`).  The include chain it needs (when the Makefile
uses `--no_default_includes`):

```
--include $lib/fstar/pulse/common          # Pulse.Lib.Core, Pulse.Main (fsti)
--include $lib/fstar/pulse/common.checked
--include $lib/fstar/pulse/pulse/lib       # Pulse.Lib.Array, Pulse.Lib.Vec, …
--include $lib/fstar/pulse/pulse.checked
```

- Skip re-verifying the Pulse stdlib with
  `--already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore`.
- **Seed the `--cache_dir`** with pre-verified `*.checked` or Error 317
  ("Expected Prims to be already checked") fires.  The three sources are
  (a) `$FSTAR_CHECKED/*.checked` (the `fstar-checked` flake input, exported as
  `FSTAR_CHECKED` by the flake devShell; the Makefile's `--include $(FLIB)/ulib`
  dir has **no** `.checked`), (b)
  `$(fstar.exe --locate_lib)/pulse/common.checked/*.checked`, and (c)
  `$(fstar.exe --locate_lib)/pulse/pulse.checked/*.checked`.  Copy all three
  into the cache dir — ~517 files; `Prims.fst.checked` only exists via (a).

### Backend enum (authoritative)

> ⚠ **`--codegen` takes `C`, NOT `Custard`.**  Measured 2026-11-17 on
> `v2026.11.15+lsp`: `--codegen Custard` fails with
> `error: wrong argument given to option 'codegen'` and the option's own help
> prints `<OCaml|FSharp|KrmlC|KrmlRust|C|Cherry|Plugin>`.  The **frontend** is
> Custard; the **backend selector** is `--custard_backend`, and the
> `--codegen` value is just the target language.  Older notes that write
> `--codegen Custard` are wrong for this toolchain.

`--custard_backend` accepts exactly **`OCaml` (default) | `FSharp` | `KrmlC` |
`KrmlRust` | `C`**.  There is **no wasm**.  `--codegen` additionally accepts
`Cherry` (C + reference-counted heap cells, experimental) and `Plugin`.

| Backend | Notes |
|---|---|
| `OCaml` | legacy ML; monomorphic-only for C-like layout |
| `C` | direct C11; requires `--custard_monomorphize_types true` |
| `KrmlC` / `KrmlRust` | legacy re-ingest path (named after the retired extractor); `KrmlRust` broken upstream (431 rustc errors) |
| `FSharp` | `.NET 10`; separate follow-up |

Custard's C backend emits only `<stdint.h>`, `<stdlib.h>`, `<stdbool.h>`,
`<string.h>` (plus `typedef uint8_t custard_unit;`) and compiles with
`-Wall -Wextra -Werror`.

### Required flags for direct C

```bash
fstar.exe --codegen C \
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
  **only those two named roots** — the individual leaf functions are **not**
  independently callable, and the roundtrip `Lemma`s are erased in any case.
  A claim like "18 API fns + 9 roundtrip lemmas exported" is **false** for a
  single-root build; the only exported surface is the dispatch pair (plus
  whatever `type`s the roots need).  If the *full* surface must be exported,
  use `--custard_entry_module`, and then `noextract`-guard every spec-only def
  you don't want rooted (see "the three rules", item 1).

- A **library has no `main`** — use `--custard_entry_module`, not
  `--custard_main`.  For **several independent leaves in one package**, see the
  "one root file + `--custard_entry`" recipe in §6 — looping the extractor is
  the silent-empty-artifact trap.

### C layout choices

- record → `struct`; all-nullary constructor variant → `enum`;
  single-constructor variant → plain `struct` (no tag/union; keeps tuples/1-ctor
  records free); anything else → tagged union (`enum tag` + `union`).
- matching → **if/else-if chain** (not `switch`) — so a tagged union return
  (e.g. `decode_result_c`) is fine: no struct-return trap.
- constructor applications → C99 compound literals with designated initializers.
- `decode_result_c` (tagged union) **returns by value cleanly** — no out-param
  refactor needed.

### Backend matrix (verified)

| Backend | Mechanism | Status |
|---|---|---|
| `ocaml` | `--codegen OCaml` (legacy ML) | ✅ pure spec extracts (no Pulse needed) |
| `native` (C) | `--custard_backend C` (direct C11) | ✅ Pulse leaf extracts + compiles |
| `fsharp` | `--codegen FSharp` / `--custard_backend FSharp` | 🟡 `.NET 10`, separate follow-up |
| `rust` | `--custard_backend KrmlRust` | ❌ dead upstream |
| `wasm` | — | ❌ gone (no backend) |

### `Tot` does NOT block extraction — *pure types* do

"What gates a backend?" is answered by the *types in runtime bodies*, not by
the effect:

| Module kind | Traits | Extracts to |
|---|---|---|
| pure spec (`Seq`/`list`/`nat`/`int`, `Tot`, `Lemma`) | no C repr | **OCaml only** (`--codegen OCaml`) |
| Pulse leaf (`fn`, `U32.t`/`U8.t`, `A.array`, `Int.Cast`) | C-safe | **C + OCaml + F#** (Custard) |

The Pulse leaf's *spec* (in `ensures`/`noextract` helpers) may mention `Seq`/
`find_candidate` (erased), but its *runtime body* must stay in `U32.t` + `A.array`
+ Pulse primitives.  This is the reference split: `Data.Codec.Types`/
`Data.Codec` → OCaml; `Data.Codec.Pulse` → C/OCaml/F#.

---

## 16. The Pulse idiom that costs the most time (0-admit, extracted to clean C11)

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
   `pure`.  The canonical pattern is
   `Pulse.Lib.Array.PtsToRange.pts_to_range_index` (bounds as `Ghost.erased
   nat` implicit args).
2. **Never use `U32.v` / `U8.v` / nat `%` in extracted bodies** — `Prims.int`
   has no C representation (Error 368).  Use `FStar.Int.Cast` narrow/widen
   casts: `uint32_to_uint8`, `uint8_to_uint32`.  `U32.v` is fine in specs/`pure`
   (erased).
3. **`U32.add i k` needs an overflow precondition** `U32.v i + k < 4294967296`
   in `requires`.

### Spec functions must be `noextract`

Pure spec helpers (`varint_encode_pred`, `varint_decode_expected`) reference
`Seq`/`Prims.int` and are rooted by `--custard_entry_module`.  Mark them
`noextract` so Custard skips them (it "passes over silently" `noextract` roots)
— otherwise Error 368 (`Prims.int` has no C representation).

### Making the post-multibyte cases prove

`word32be`/`word32le` encoders must use **`U32.div`/`U32.rem`** (not
`U32.shift_right`) so the byte extraction *syntactically* matches the pure
`*.enc` division structure (`v / 16777216`, `(v / 65536) % 256`, …).  Shifts
would require a shift→bytes bridge lemma that no longer exists.

### Roundtrip lemmas are *easy* (unexpectedly) — **EXCEPT varint**

Because the pure `codec` record's `.enc`/`.dec` are **computable projections**,
`dec (enc x)` reduces to `Inr (x, n)` and SMT discharges the roundtrip lemma
automatically — no heap threading at all.  The `token`/`byteval`/`uint8`/
`word16*`/`word32*` roundtrip lemmas verify with zero manual frame reasoning.
`word32be`/`word32le` are *rlimit-sensitive* but terminate (slow, ~90s each at
`--z3rlimit 120`).

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
proving `n = 128*(n/128) + n%128` and the multi-byte analogues.  The Pulse
module adds:

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

Rules learned:

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
3. **The hang is z3 at 100% CPU, not 0%.**  The "0% CPU / `stopped`" heuristic
   is only *one* hang signature.  This varint query blazes at ~100% CPU for
   minutes (`ps -o pcpu=,time=` accumulates 1s CPU per 1s wall) and never
   returns; treat *both* 0%-stopped and 100%-spinning-anomalously-long as hangs;
   bisect rather than wait.
4. **Bisecting a `#lang-pulse` module by truncation is off-by-one prone.**
   A `fn`'s body-closing `}` is NOT its last `}` — the `match c { … }` and the
   body `{ … }` are two separate depths, so `head -N` at the wrong `N` leaves
   `brace depth == 1` and F\* reports a bare `Syntax error` at EOF.  Count
   `{}`/`()` balance (a 10-line Python scanner that skips `(* … *)`) before
   each truncation; the green cut points for one module were
   (encoders+decoders) `head -719`, (+dispatchers) `head -863`,
   (+through word16le) `head -974`, etc. — **never** `head -862`.
5. **`varint_decode_expected`/`varint_encode_pred` remain `noextract`** even
   with the SMTPat lemma added; the lemma itself is `noextract` and references
   `Seq`/`Prims.int`, so it must not be rooted.

### `Pulse.Lib.Array.alloc` / `.free` are deprecated but functional

`A.alloc x n` / `A.free a` carry `[@@deprecated "…unsound; only use for model
implementations"]` (Warning 288) but **verify green and extract**.  The
non-deprecated scoped form is `A.with_local init len (fun arr -> body)`, but its
signature (universe-polymorphic `ret_t` + `pre`/`post` slprops) is finicky to
call directly; `alloc`+`free` is the pragmatic choice for a scoped buffer test
(the deprecation is a warning, not an error, and does not gate the build).

### `label` is a **reserved Pulse keyword**

A `#lang-pulse` module cannot use `label` as a combinator name OR a record
field name (`{ …; label = … }` or `{ r with label = … }`) — the parser rejects
it with a bare `Syntax error`.  Concretely: a codebase whose pure spec defines
`label : string -> codec a -> codec a` and a `decode_error` record with a
`label` field **cannot** mix those pure definitions into a `#lang-pulse` module.

**Fix:** split pure tests/definitions (that use `label`) into a plain module,
and put only the buffer-based code into a dedicated `#lang-pulse` module.  Do
not try to `open` the `label`-bearing module from `#lang-pulse`.

---

## 17. Common errors in the Custard/Pulse surface

| Error | Meaning | Fix |
|---|---|---|
| 19 (timeout, word32 roundtrip) | low z3 rlimit | `--z3rlimit 120` |
| 317 | `--already_cached X` but cache lacks `X.fst.checked` | seed cache with stdlib `.checked` (§15) |
| 368 | `Prims.int` reached extraction | `noextract` the spec fn; `FStar.Int.Cast` in bodies |
| 134 / 285 | `Pulse` namespace not found | add the four `pulse/*` `--include` paths (or drop `--no_default_includes`) |
| 180 (`Unexpected operator **`) | `#lang-pulse` not active | load the Pulse lib (`open Pulse`); ensure `#lang-pulse` + Pulse includes |
| 10 | OCaml codegen batch of many files | one file per `--codegen OCaml` run |
| 66 (implicit `p` only in pre/post) | `FStar.Classical.forall_intro_2/3/4` predicate not inferable | annotate `#a`/`#b`/`#p` explicitly (§20) |
| — (hang, varint roundtrip) | 100% CPU z3, non-terminating roundtrip `fn` | SMTPat structural lemma (§16) |

---

## 18. Carry-over facts: `decreases` arithmetic, `forall_intro_2`, `assert_norm`

Three measured facts that every new module runs into.  (For the fourth —
`U8.t` is opaque, so wrapping byte arithmetic goes through `v`/`v_inj` — see
[fstar-stdlib §14](../fstar-stdlib/SKILL.md).)

### Arithmetic `decreases` clauses are BROKEN — use a bare variable or a list subterm

Writing a subtraction of two **bare variables** in a `decreases` clause fails
to parse:

```fstar
let rec go (i: nat) ... : nat (decreases (n - i)) = ...  -- ERROR 208
  (* Unexpected term: ((decreases (-(n, i)))) *)
```

The `-` between two nats inside `decreases (…)` is parsed as a *negated
tuple*, not subtraction.  (`decreases n` and `decreases (n + 1 - k)` written
*bare* also error the same way.)  The working forms:

```fstar
let rec pow2 (n: nat) : Tot int (decreases n) = ...           -- bare nat
let rec bytes_decode (bs: list byte) ... (decreases bs) = ... -- bare list/subterm
```

**Rule:** recurse on a *bare* `nat` or on the *subterm of a list/tuple* (F\*'s
structural order), and return `Tot` — `: Tot (option elem) (decreases ls)`.  Do
NOT use `Seq.length s - i` or any arithmetic in `decreases`.

**REFINEMENT (verified on `Data.Image.PNG.Filter`):** the parse error fires on a
*bare-variable* `n - i` only.  `decreases (length l - i)` where `length l` is a
**function application** (`List.Tot.length l`, not a bare `n`) parses and
verifies fine — used 4× in `lemma_sub_rt`/`lemma_up_rt`/`lemma_average_rt`/
`lemma_paeth_rt` (each `(decreases (length row - i))`, recursing on `i+1`
guarded by `i < length row`).  So: bare `n - i` = ERROR 208; `f l - i` (a call
minus a var) = OK.  Prefer list-subterm recursion anyway.

### `FStar.Classical.forall_intro_2` (and `_3`/`_4`) needs explicit implicit args (Error 66)

A bare `FStar.Classical.forall_intro_2 f` where `f` returns a `Lemma` fails to
resolve its implicit predicate `#p` (and dependent `#b`):

```fstar
(* FAILS — Error 66: Failed to resolve implicit argument ?52 of type
   x: char -> _: list byte -> prop, introduced for Instantiating implicit
   argument 'p'.  "This implicit argument only occurs in a pre- or
   postcondition, so it cannot be inferred." *)
FStar.Classical.forall_intro_2 (fun c rest -> lemma_utf8_decode_prefix c rest)
```

Fix: annotate all three implicits explicitly:

```fstar
FStar.Classical.forall_intro_2
  #FStar.Char.char
  #(fun (_: FStar.Char.char) -> list byte)          (* the dependent b *)
  #(fun (c: FStar.Char.char) (rest: list byte) ->
       utf8_decode_one (char_to_utf8 c @ rest) == Some (c, rest))
  (fun c rest -> lemma_utf8_decode_prefix c rest)
```

`forall_intro_3`/`forall_intro_4` are the same shape (one more `#b` per
quantifier).

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

`string_to_bytes` ultimately calls `FStar.String.list_of_string`, which only
reduces on a *literal* string, and `assert_norm` only normalizes closed terms.
When a `Lemma`'s body fails at rlimit 40 with an `assert_norm` on a `let`-bound
var, inline the `let`.  (Same mechanism on the proof side:
`fstar-proofs` §91 trap 2.)

---

## 19. Reordering or splitting a proof-heavy module

### Extract units by balanced `#push`/`#pop`, never by walking comments backward

To reorganize a large `.fst` (e.g. 163 defs, 80 lemmas) into "layers, each
sorted", do **NOT** write one line-based splitter that walks backward over
`(** *)`/`(* *)` comments to find each def's verbatim block.  A handful of defs
have *inconsistent* doc-comment placement (a duplicated doc comment, a `(* *)`
block and `#push-options` sandwiched between a section header and its def,
`codec` as a `type` wrapped in its own `#push`/`#pop`), so
backward-comment-walking silently mis-splits units and gives a
`#push`/`#pop` imbalance (which corrupts the module).

The reliable unit boundary is the **balanced `#push-options`/`#pop-options`
pairing** — a def's block ends at its `#pop-options`, full stop.  Then reorder
**incrementally, layer by layer**:

1. Extract all units; assert 0 `#push`/`#pop` imbalance per unit, 0 overlap, 0 gap.
2. Classify each def into a semantic layer (core types → helpers → proof
   lemmas → combinators → expansion lemmas).
3. Sort **within** each layer by topological+alphabetical order — NOT pure
   alphabetical, because F\* requires definition-before-use and lemmas form a
   DAG (a single alphabetical lemma block is NOT feasible: `Data.Codec.Types`
   has 23 lemma→lemma edges + edges to non-lemma helpers).
4. Re-verify `make check` (0-admit) after **every** move.  F\* is the ordering
   oracle: an out-of-order reference surfaces as "not found in scope" (Error
   72/241) and is fixed by moving *that one* dependency earlier — don't re-sort
   the whole layer.

Distinguish **proof lemmas** (used *by* combinators) from **expansion lemmas**
(`lemma_{map_,product,byte_val,digits_to_int}_*_eq`) which document a
combinator's `.wfcv`/`.rest_cond`/`.enc`/`.dec` and therefore must come *after*
that combinator.

### Splitting a module: compute the tier closure before moving anything

Learned splitting `Data.Codec.Types` (4,133 lines) into core +
`Data.Codec.Text`.  **All of the traps below produce a green build** — that is
the whole point of this section.  (The three build-system traps —
`make check` does not track deps, `include` ≠ `open`, unclosed `(** *` — are
[fstar-build §10b](SKILL.md), [fstar-lang §2](../fstar-lang/SKILL.md) and
[fstar-docs §12](../fstar-docs/SKILL.md).)

Before moving symbol `s` out of core, ask which other moved symbols (and which
*remaining* core symbols) reference `s`.  A dependency edge core → new-module
is a cycle and cannot be built.  Compute it mechanically:

```python
# for each candidate binary symbol, which core symbols reference it?
used = {n for n in candidates
        if re.search(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_])', core_text)}
```

In one package this revealed that `varint` (a core leaf) calls
`varint_encode_go`, and `word32be/le` call `lemma_word32_enc_bytes`, and
`digits_to_int` is itself core — so **29 of 35** candidate symbols had to stay
in core.  Discovering that *after* writing the new module is how you get a
103-line module that does not deliver the split it advertises.

Also check the extraction layer: a `#lang-pulse` module that names leaves via
`module DC = Data.Codec.Types` pins those leaves to core, because retargeting
the alias is a source change and some changes freeze their downstream consumers.

### `pow2`-style helpers look like leaf material but are core vocabulary

A helper used by the very symbols you are *moving* must stay where the movers
are.  `pow2` was assigned to the text tier (its only "consumer" was
`string_is_ascii`) — but it had **23 uses inside core** in varint arithmetic
(`value + piece * pow2 shift`) and `assert_norm (pow2 32 = 4294967296)`.  A
text-tier `pow2` would have made core depend on the text module: an immediate
cycle.

Grep the *whole* core for each candidate, not just its nominal consumer:

```bash
grep -cE '\bpow2\b' src/Data.Codec.Types.fst   # 23 — it is core vocabulary
```

---

## 20. Extracted-repo uniformity (verified, all 7 repos + template)

When a package is extracted to a standalone `fstar-<pkg>` repo, the repo MUST be
on par with its siblings — not partially uniform, but fully.  Audit **every
file in every repo** against this checklist.

### Byte-identical across all repos (do not diverge)

- `.gitignore` — identical string every repo (covers `out/`, `result*`, `cache`).
- `treefmt.nix` — identical (formats **nix only**; `.fst`/`.md` are deliberately
  excluded because the F\* formatter is broken upstream, see
  [fstar-docs §11](../fstar-docs/SKILL.md)).
- `LICENSE.md` — the AGPL body after the name blurb is byte-identical.

### Uniform-with-per-package-name files

- `LICENSE.md` blurb — the exact pattern is `<name> — a formally verified
  <desc> written in F\*.`  Do NOT drift to "a verified … that extracts to
  C/OCaml/F# via Custard" — that was the template's phrasing and leaked into an
  extracted repo.
- `CHANGELOG.md` — MUST exist in **every** repo (library **and** the flake
  template).  Keep-a-Changelog + SemVer, with `## [Unreleased]` and
  `## [0.1.0] — initial extraction` (package-accurate `### Added` module
  lists).
- `flake.nix` `description` — `"<name> — verified <desc>"`; inputs
  `nixpkgs`/`flake-utils`/`treefmt-nix`/`fstar` uniform, plus per-package
  `fstar-*` dep inputs.
- `default.nix` — deliverable set is ALWAYS `{ checked; ocaml; native; fsharp; }`;
  `pname` drops the `fstar-` prefix; codec dep injected as `codec-src`/`codec-checked`.
- `Makefile`, `AGENTS.md`, `API.md`, `README.md` — header/structure uniform;
  README/API content is package-specific (architecture, RFC coverage, module tables).
- Copyright/SPDX header — `Copyright 2026 Department of Code LLC.` +
  `SPDX-License-Identifier: AGPL-3.0-or-later` on every `.fst`/`.nix` (and `.md`
  where used).

### Gotchas

- **No scratch dirs in a shipped repo.**  A `spike/` and `openspec/` dir that no
  other repo has is a uniformity violation (scratch `.fst`/`.c`/`.checked` and
  old change proposals).  Flag and confirm before deleting.
- **HTTPS remotes + `osxkeychain`.**  Set `origin` to
  `https://github.com/<owner>/<repo>.git` (not `git@github.com:…`) and
  `git config --global credential.helper osxkeychain` so pushes don't prompt for
  SSH passwords.  The first HTTPS push caches a PAT.

### Downstream-repo OCaml extraction: extract the dep's pure spec locally, not the wrapped library

A repo that *depends* on an extracted library and wants its own `ocaml` target
hits a cross-repo module-resolution trap.  The dependency's flake `ocaml`
package **wraps** its modules into a namespace (dune `(wrapped true)` default),
so the downstream's extracted `.ml` files — which reference the *bare* top-level
`Data_Codec_Types` / `Data_Codec` — fail with:

```
File "Data_BaseN_Base32.ml", line 2: Error: Unbound module Data_Codec_Types
```

Do **not** link the downstream into the wrapped package.  Instead, in the
downstream's `ocaml-src` derivation, **extract the dep's pure spec
(`Data.Codec.Types` + `Data.Codec`) locally** via `--codegen OCaml` from the
dep's flake input, compile those `Data_Codec_Types.ml`/`Data_Codec.ml` into the
downstream's own dune library (unwrapped), and drop the wrapped findlib dep:

```nix
# in ocaml-src buildPhase, before extracting your own pure modules:
for m in Data.Codec.Types Data.Codec; do
  ${fstar-exe} --no_default_includes --include "$ULIB" --include ${codec-src}/src \
    --cache_checked_modules --cache_dir cache --odir cache ${codec-src}/src/$m.fst || exit 1
  ${fstar-exe} … --codegen OCaml --odir $out ${codec-src}/src/$m.fst || exit 1
done
# dune: (modules …your-modules… Data_Codec_Types Data_Codec Custard)
#        (libraries fstar.lib)   ← NO wrapped dep
```

No `Custard` collision: you only extract the codec *pure* spec, never its Pulse
leaf (the leaf is what emits `Custard.ml`).

### Local sibling flake deps: `git+file:///abs/path`, not `path:../`

When a new repo consumes a *local sibling* flake, `path:../sibling` resolves
fine as a URL but **fails during `nix flake lock`** (`error: '...' is too short
to be a valid store path` / pure-eval path restriction).  Use
`git+file:///absolute/path/to/sibling` instead — it locks to the sibling's HEAD
commit; switch to the published `github:<owner>/<repo>` input when the repo
ships.

## 21. A `nix build` that sits at 0% CPU is a HANG, not a slow build — bypass it and extract directly

Verified 2026-11-17 on `fstar-codec` (`v2026.11.15+lsp`, aarch64-darwin).  The
`native` derivation re-verifies `Data.Codec.Types` from cold **inside its own
sandbox**, and that `fstar.exe` sat at **0% CPU for 15+ min** with no output —
twice, in two separate invocations.  The same freeze reproduces when the
derivation's verify loop is run by hand.  Per Mandate 3 the process is
*stuck*, not working; `sleep` and retry is the wrong response.

### The tell

| symptom | meaning |
|---|---|
| `fstar.exe` at **0% CPU**, no stdout for minutes | stuck (non-terminating SMT query, or a blocked sandbox step) |
| 100% CPU for many minutes | slow but working — a different problem |
| `nix build` prints `building '...drv'...` then nothing | it is inside the derivation; you cannot see which module |

### What to do instead

Do **not** fight the derivation.  Run the two stages it performs, in your own
shell, where you can see each module and put a hard timeout on each:

```bash
# 1. verify into a SHARED cache, one module at a time, timeout-guarded
nix develop -c fstar.exe --no_default_includes --include "$ULIB" $PULSE_INCS \
  --include ./src \
  --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
  --z3rlimit 120 --cache_checked_modules --cache_dir cache --odir cache \
  src/<Mod>.fst

# 2. extract from that cache, once, rooted
nix develop -c fstar.exe --no_default_includes --include "$ULIB" $PULSE_INCS \
  --include ./src --include cache \
  --already_cached Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore \
  --cache_checked_modules --cache_dir cache \
  --codegen C --custard_backend C --custard_monomorphize_types true \
  --custard_entry <Mod>.encode_bytes --custard_entry <Mod>.decode_bytes \
  --odir out src/<Mod>.fst
```

This produced `Custard.c` / `Custard.h` and compiled clean with
`-Wall -Wextra -Werror` **in the same session** where `nix build` never got
past module 1.  The manual path also tells you *which* module is slow, which
the derivation's silence hides.

### One measured detail that costs time

**`--codegen C`, not `--codegen Custard`** (§15).  The wrong value fails
instantly with `wrong argument given to option 'codegen'` — but inside a
derivation that failure surfaces only *after* the long verify stage, so it
reads as yet another hang.  Get the extraction command right and tested
outside the derivation first.

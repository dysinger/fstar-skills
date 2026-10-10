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

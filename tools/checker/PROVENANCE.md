# Provenance: the `axiom-checker` binary (Route B's closure oracle, environment path)

`#print axioms` is syntax, and syntax is an environment extension: a candidate can install a
`syntax`/`macro_rules` pair for it, and the extension crosses imports. Measured here (the attack
below): a module `Evil` defines a macro for the command that prints `'Evil.foo' depends on axioms: []`
and leaves `Evil.foo` a `sorry`; a *different* file whose entire text is

```lean
import Evil

#print axioms Evil.foo
```

prints `'Evil.foo' depends on axioms: []` — the fake fires from the importing file and Lean's real
report never runs. A closure check that reads the candidate's own elaboration output therefore reads
something the candidate can write.

This binary is the answer: it never parses Lean source, so no candidate syntax can reach it. It loads
the candidate's elaborated module through `Lean.importModules` against a `LEAN_PATH` the harness
builds, resolves the declaration by name, collects its axioms through `Lean.collectAxioms`
(`Lean.Util.CollectAxioms`) — the environment's constant bodies plus the axiom-dependency data the
kernel recorded in the oleans — and prints them. This file is the record.

## Pin

| | |
| --- | --- |
| Toolchain | `leanprover/lean4:v4.35.0-rc3` (`tools/checker/lean-toolchain`, byte-identical to `proofs/lean/token-ring/lean-toolchain` and to the vendored `tools/repl/lean-toolchain`; sha256 `bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47`) |
| Upstream dependencies | none — `lake-manifest.json` has `"packages": []`, so the build is bare Lean core: no Mathlib, no `lake exe cache get` |
| Built binary | `tools/checker/.lake/build/bin/axiom-checker` (a gitignored build artifact: the repository root `.gitignore` ignores `.lake/`) |
| Sources | `tools/checker/AxiomChecker.lean` (the library: search path, resolution, collection, output), `tools/checker/AxiomChecker/Main.lean` (argument handling and the exit code), `tools/checker/lakefile.toml` |
| Provisioned | 2026-09-26, on this host, via `nix develop -c` |

### Why the toolchain is the pin and not a free choice

The binary imports the candidate's olean, so its Lean must be the Lean that wrote it — a different
build would refuse the olean or, worse, read a different frontend's data. `v4.35.0-rc3` is the pin
every other moving part here uses (Mathlib's release, `proofs/lean/token-ring/lean-toolchain`,
`tools/repl`).

## Vendored sources

`tools/checker/` holds only this project's own files — nothing is vendored. Digests of the sources the
binary was built from (sha256):

```
ae9e29f989760bafa1fa586524c27a1f10bbe997e4331b00ea71654a736f72c4  AxiomChecker.lean
21e9e312eb25a202e2844e9a885ff329535ab0edce931445af57fc75d8d79933  AxiomChecker/Main.lean
281dde7b0a92209f5360467d77312fb08319ca7b24c251b345c5308b5a184e4f  lakefile.toml
```

`supportInterpreter = true` in `lakefile.toml`, as in `tools/repl`: importing a module with
`loadExts := true` may evaluate imported extension data.

## Output contract

One item per line on stdout:

```
axioms <count>
<axiom name>
<axiom name>
...
resolved <fully qualified declaration name>
```

* `axioms <count>` is always the first line. The bracket form the candidates have been forging
  appears nowhere in the output.
* `resolved <name>` is the last line and names the declaration the set belongs to, so a resolution
  that is not the one the caller meant is visible instead of being absorbed into a plausible set.
* A run that cannot answer prints **no** `axioms` line, writes the reason to stderr, and exits
  non-zero: "I could not find it" and "it has no axioms" are never the same answer.

Arguments: `axiom-checker <Module> <theorem-simple-name>` (e.g. `axiom-checker TokenRing mutex`). The
declaration is looked up as `<Module>.<name>` first and then as the bare `<name>`: the seed declares
its theorem inside `namespace TokenRing` (so `TokenRing.mutex`) while the argument is namespace-less,
and a root-level declaration of the same simple name must not shadow the seed's theorem. Which one
resolved is printed (`resolved …`).

## Build recipe

From a clean checkout (or after `rm -rf tools/checker/.lake`), with the toolchain available (the dev
shell provides `elan`), run from the repository root:

```sh
nix develop -c bash -c 'cd tools/checker && lake build'
```

Observed build (2026-09-26), from scratch — no Mathlib, no cache fetch, so it is seconds:

```
✔ [2/6] Built AxiomChecker (488ms)
✔ [3/6] Built AxiomChecker.Main (455ms)
✔ [4/6] Built AxiomChecker:c.o (424ms)
✔ [5/6] Built AxiomChecker.Main:c.o (105ms)
✔ [6/6] Built «axiom-checker»:exe (4.6s)
Build completed successfully (6 jobs).
```

The binary lands at `tools/checker/.lake/build/bin/axiom-checker`.

## Elaborating a candidate the harness's way

`lean` takes the *module name* from the **source path** relative to its root directory (the current
directory, or `-R`), not from `-o`; measured, and it is a real trap: elaborating `Weird.lean` with
`-o <dir>/TokenRing.olean` produces an olean that `import TokenRing` will load with no name-mismatch
error, and then the declarations are the `Weird` ones. So the harness must place the candidate as
`<root>/TokenRing.lean` and run lean there:

```sh
cd <tmpdir with the candidate as TokenRing.lean>
LEAN_PATH=$PKG_DEPS <toolchain>/bin/lean -o <tmpdir>/TokenRing.olean TokenRing.lean
```

`LEAN_PATH` for the elaboration is the package's dependency closure plus the toolchain's own library
directory; `lake env` prints exactly it (`LEAN_PATH=<each dependency>/.lake/build/lib/lean` … plus
`proofs/lean/token-ring/.lake/build/lib/lean` and `<toolchain>/lib/lean`). No `lake` in the *checker*
invocation: the candidate's shell can reach the package's lakefile, so a `lake`-constructed
environment is not trustworthy.

## Observed runs

Elaborated as above (`LEAN_PATH` = the package's dependency closure + `<toolchain>/lib/lean`), then:

```
$ LEAN_PATH=<tmpdir>:<package deps>:<toolchain>/lib/lean axiom-checker TokenRing mutex
```

1. **Real artifact** (`proofs/lean/token-ring/.runs/TokenRing-r1.lean`, the closed proof), exit 0:

```
axioms 3
Classical.choice
Quot.sound
propext
resolved TokenRing.mutex
```

2. **Seed** (`proofs/lean/token-ring/TokenRing.lean`, the `sorry`), exit 0:

```
axioms 4
Classical.choice
Quot.sound
propext
sorryAx
resolved TokenRing.mutex
```

3. **The attack**, side by side. The elaborated `Evil` module, then a file that only imports it and
   asks the question (exit 0):

```
'Evil.foo' depends on axioms: []
```

   — and the checker on the same olean, exit 0:

```
axioms 1
sorryAx
resolved Evil.foo
```

   The forgery is on the screen and the checker is not looking at that screen.

4. **Renamed theorem** (module `Renamed` declares `TokenRing.mutex_renamed`): stdout empty, exit 1,
   stderr

```
uncaught exception: no declaration named 'mutex' in module 'Renamed': tried 'Renamed.mutex', 'mutex'
```

5. **A second declaration with the same simple name**: module `TokenRing` holding `TokenRing.mutex`
   (`sorry`) plus `Other.mutex` and a root-level `mutex`, both trivially provable — the checker
   reports `axioms 1` / `sorryAx` / `resolved TokenRing.mutex`, i.e. the seed's theorem, and the
   decoys' empty axiom sets are not what it prints. For contrast, the same invocation against a module
   whose only `mutex` is the root-level one prints `axioms 0` / `resolved mutex`: the resolved name is
   what tells the two apart.

## What `importModules` needs

* The olean itself, plus the **whole transitive import closure** of every module it imports — for a
  Mathlib-importing candidate that is the Mathlib oleans too, all of it on `LEAN_PATH`. The olean
  alone is not enough; the harness must pass the same path it elaborated with (plus the tmpdir first,
  so the candidate's module wins over the package's own pre-built `TokenRing.olean`).
* No `.ilean`, no `.trace`, no `.olean.private`: not needed, not read here. (`loadExts := true` reads
  the extension data that is already inside the `.olean`.)
* `enableInitializersExecution` must be called before the import, as `importModules` documents for
  `loadExts := true`. Measured: the candidate's `initialize`/`#eval` code does **not** run in this
  process, so a candidate cannot print into the checker's stdout.
* If the module or the declaration is missing, the failure is loud: non-zero exit, stderr message.

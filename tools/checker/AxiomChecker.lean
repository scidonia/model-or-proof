/-
The axiom checker: report the axiom set of a named theorem from Lean's own elaborated environment.

Why this is a separate prebuilt binary rather than a source-level print-axioms line: that command is
syntax like any other, so a candidate can install a `syntax`/`macro_rules` pair for it, and syntax is
an environment extension — it crosses imports. A file that only writes `import Evil` and then asks
the question prints whatever `Evil`'s macro says, and Lean's real answer never runs (observed; see
PROVENANCE.md). Nothing here parses Lean source, so nothing here can be reached by a candidate's
syntax: this binary reads the elaborated module's constant map and the axiom-dependency data the
kernel wrote into the olean.

Output, one item per line on stdout:

    axioms <count>
    <axiom name>
    <axiom name>
    ...
    resolved <fully qualified declaration name>

`axioms` is always the first line, so the count cannot be confused with anything else, and neither the
phrase nor the bracket form the candidates have been forging appears anywhere in this output.
`resolved` is the last
line and names the declaration the set belongs to: a candidate that smuggles in a second declaration
with the same simple name shows up as a resolved name nobody asked for rather than as a plausible
set. A run that cannot answer prints no `axioms` line at all, writes an explanation to stderr, and
exits non-zero — "I could not find it" must never read as "it has no axioms".
-/
import Lean

open Lean

namespace AxiomChecker

/-- The module search path.

`LEAN_PATH` is authoritative: the harness builds it and the invocation deliberately has no `lake` in
it (a candidate's shell can reach the package's lakefile, so a `lake`-constructed environment is not
trustworthy). The toolchain's own library directory is appended when the sysroot can be determined,
which is what makes a manual run work without a prepared `LEAN_PATH`; failure to determine it is not
fatal, because the environment variable is the intended source. -/
def initSearchPathForChecker : IO Unit := do
  let fromEnv ← addSearchPathFromEnv ∅
  match ← try some <$> findSysroot catch _ => pure none with
  | some sysroot => searchPathRef.set (fromEnv ++ (← getBuiltinSearchPath sysroot))
  | none         => searchPathRef.set fromEnv

/-- The fully qualified name of the declaration to report on.

The seed declares its theorem inside a namespace (`namespace TokenRing`, so `TokenRing.mutex`), while
the argument arrives namespace-less; a seed that declares at the root has a bare name. Both are
tried, the module-qualified form first: the seed's theorem is the namespaced one, so a candidate that
adds a root-level declaration of the same simple name must not be able to shadow it. Which name
resolved is printed, so a resolution that is not the one the caller meant is visible. -/
def resolveDeclaration (env : Environment) (moduleName theoremName : Name) : IO Name := do
  let candidates := #[moduleName ++ theoremName, theoremName]
  for candidate in candidates do
    if env.find? candidate |>.isSome then
      return candidate
  let tried := String.intercalate ", " (candidates.toList.map fun c => s!"'{c}'")
  throw <| IO.userError <|
    s!"no declaration named '{theoremName}' in module '{moduleName}': tried {tried}"

/-- The axioms `declName` depends on, through Lean's own `CollectAxioms`: the environment's constant
bodies plus the dependency data already recorded in the imported oleans. Never the source text. -/
def axiomsOf (env : Environment) (declName : Name) : IO (Array Name) := do
  let ctx : Core.Context := { fileName := "<axiom-checker>", fileMap := default }
  Lean.Core.CoreM.toIO' (collectAxioms declName) ctx { env := env }

/-- Report the axiom set of `theoremName` as elaborated in `moduleArg`. -/
unsafe def check (moduleArg theoremArg : String) : IO Unit := do
  let moduleName := moduleArg.toName
  let theoremName := theoremArg.toName
  initSearchPathForChecker
  -- Required before an import that loads environment extensions; see `importModules`'s `loadExts`.
  enableInitializersExecution
  let env ←
    try
      importModules #[{ module := moduleName }] {} 0 (loadExts := true)
    catch e =>
      throw <| IO.userError s!"cannot load module '{moduleName}': {e.toString}"
  let declName ← resolveDeclaration env moduleName theoremName
  let axioms ← axiomsOf env declName
  -- Lexicographic by name, so the report is stable and does not depend on the collector's internal
  -- ordering (the API returns a name-ordered array, whose `Name.lt` order is not the printed one).
  let axioms := axioms.qsort fun a b => a.toString < b.toString
  let out ← IO.getStdout
  out.putStrLn s!"axioms {axioms.size}"
  for ax in axioms do
    out.putStrLn ax.toString
  out.putStrLn s!"resolved {declName}"
  out.flush

end AxiomChecker

import AxiomChecker

/-- `axiom-checker <Module> <theorem-simple-name>`; see `AxiomChecker.check` for the output contract.

Exit 0 when a set was printed, 2 on a malformed invocation, and non-zero (with a message on stderr)
when there was no set to print. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleArg, theoremArg] =>
    AxiomChecker.check moduleArg theoremArg
    return 0
  | _ =>
    IO.eprintln "usage: axiom-checker <Module> <theorem-simple-name>"
    return 2

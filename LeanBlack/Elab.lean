/-
  Elaborate an LLM-proposed GuardedMod by delegating to Lean itself.

  We don't write an elaborator. We write the proposal to a temp file
  wrapped as a Lean module that:
    1. imports LeanBlack.Tower
    2. defines `proposal : GuardedMod := <LLM source>`  (Lean type-checks)
    3. runs the policy check and prints ADMITTED / REJECTED

  Then we spawn `lake env lean --run` on it. Non-zero exit = elaboration
  failed; the Lean compiler's stderr is the error message we hand back
  (and, indirectly, what we'd feed to the LLM on retry).

  Dependencies: `lake` on PATH, the `lean-black` project built (so
  `LeanBlack.Tower` is importable), invoked from the project root.
-/

import LeanBlack.Tower

namespace LeanBlack.Elab

inductive Result where
  | elabError (msg : String)
  | admitted
  | rejected
  deriving Repr

instance : ToString Result where
  toString
    | .elabError m => s!"ELAB-ERROR: {m}"
    | .admitted    => "ADMITTED"
    | .rejected    => "REJECTED"

structure Config where
  wrapperPath : String := "/tmp/leanblack-proposal-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`
      and have the project built so `LeanBlack.Tower` resolves. Defaults
      to the inherited cwd. -/
  workingDir  : Option String := none

def defaultConfig : Config := {}

private def buildWrapper (proposalSrc : String) : String :=
  s!"import LeanBlack.Tower

def proposal : GuardedMod where
{proposalSrc}

def main : IO Unit := do
  if witnessPolicy stdWitnesses proposal stdRule then
    IO.println \"ADMITTED\"
  else
    IO.println \"REJECTED\"
"

/-- Send the LLM's proposed term through Lean and the policy gate. -/
def checkProposal (cfg : Config) (proposalSrc : String) : IO Result := do
  IO.FS.writeFile cfg.wrapperPath (buildWrapper proposalSrc)
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", cfg.wrapperPath]
    cwd := cfg.workingDir
  }
  -- Lean prints diagnostics to stdout (file:line:col messages) AND to stderr
  -- depending on the kind. Concatenate both for the error case.
  let combined := (out.stdout ++ out.stderr).trim
  if out.exitCode != 0 then
    return .elabError combined
  -- main's print is the last line of stdout on success.
  let lines := out.stdout.trim.splitOn "\n"
  let verdict := lines.getLast?.getD ""
  if verdict == "ADMITTED" then
    return .admitted
  else if verdict == "REJECTED" then
    return .rejected
  else
    return .elabError s!"unexpected runtime output:\n{combined}"

end LeanBlack.Elab

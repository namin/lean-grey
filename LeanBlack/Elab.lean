/-
  Elaborate an LLM-proposed GuardedMod by delegating to Lean itself.

  We don't write an elaborator. The runner writes a wrapper Lean file
  that:
    1. imports LeanBlack.Tower
    2. defines each previously-admitted mod as `admitted_i : GuardedMod`
    3. defines `proposal : GuardedMod where <LLM source>`
    4. defines `witness : Val × List Val := <LLM source>`
    5. in `main`, runs the policy gate; on admit, evaluates the witness
       against the chain `applyMod proposal (priors.foldl applyMod stdRule)`
       and prints ADMITTED-RESULT/ADMITTED-NONE/REJECTED.

  Then we spawn `lake env lean --run` on it. Non-zero exit = elaboration
  failed; the Lean compiler's diagnostics are returned for retry.

  Dependencies: `lake` on PATH, the `lean-black` project built (so
  `LeanBlack.Tower` resolves), invoked from the project root.
-/

import LeanBlack.Tower

namespace LeanBlack.Elab

inductive Result where
  | elabError (msg : String)
  | rejected
  /-- Admitted by the policy. `witnessResult` is the `repr` of the value
      produced by `applyMod proposal chained witnessVal witnessArgs`,
      or `none` if the chained rule didn't fire on the witness. -/
  | admitted (witnessResult : Option String)
  deriving Repr

instance : ToString Result where
  toString
    | .elabError m            => s!"ELAB-ERROR: {m}"
    | .rejected               => "REJECTED"
    | .admitted none          => "ADMITTED (witness produced none)"
    | .admitted (some r)      => s!"ADMITTED → {r}"

structure Config where
  wrapperPath : String := "/tmp/leanblack-proposal-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`
      and have the project built so `LeanBlack.Tower` resolves. -/
  workingDir  : Option String := none

def defaultConfig : Config := {}

private def admittedDef (i : Nat) (src : String) : String :=
  s!"def admitted_{i} : GuardedMod where\n{src}\n"

private def admittedList (n : Nat) : String :=
  let names := (List.range n).map (fun i => s!"admitted_{i}")
  "[" ++ String.intercalate ", " names ++ "]"

private def buildWrapper
    (proposalSrc : String) (witnessSrc : String) (priors : List String) : String :=
  let priorDefs := priors.zipIdx.foldl
    (fun acc ⟨src, i⟩ => acc ++ admittedDef i src) ""
  let priorList := admittedList priors.length
  s!"import LeanBlack.Tower

{priorDefs}
def proposal : GuardedMod where
{proposalSrc}

def witness : Val × List Val :=
{witnessSrc}

def main : IO Unit := do
  if witnessPolicy stdWitnesses proposal stdRule then
    let priors : List GuardedMod := {priorList}
    let chained := priors.foldl (fun r m => applyMod m r) stdRule
    let final := applyMod proposal chained
    let (v, args) := witness
    match final v args with
    | none   => IO.println \"ADMITTED-NONE\"
    | some r => IO.println (\"ADMITTED-RESULT \" ++ toString (repr r))
  else
    IO.println \"REJECTED\"
"

/-- Send the LLM's proposed term through Lean and the policy gate.
    `priors` is the list of previously-admitted proposal sources (each
    a `where`-block body); they're spliced as named defs and folded
    into the chained rule for the witness evaluation. -/
def checkProposal (cfg : Config)
    (proposalSrc : String) (witnessSrc : String) (priors : List String)
    : IO Result := do
  IO.FS.writeFile cfg.wrapperPath (buildWrapper proposalSrc witnessSrc priors)
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", cfg.wrapperPath]
    cwd := cfg.workingDir
  }
  let combined := (out.stdout ++ out.stderr).trim
  if out.exitCode != 0 then
    return .elabError combined
  let lastLine := (out.stdout.trim.splitOn "\n").getLast?.getD ""
  if lastLine == "ADMITTED-NONE" then
    return .admitted none
  else if lastLine.startsWith "ADMITTED-RESULT " then
    return .admitted (some (lastLine.drop "ADMITTED-RESULT ".length))
  else if lastLine == "REJECTED" then
    return .rejected
  else
    return .elabError s!"unexpected runtime output:\n{combined}"

end LeanBlack.Elab

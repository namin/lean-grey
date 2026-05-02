/-
  Elaborate an LLM-proposed GuardedMod by delegating to Lean itself.

  Two-stage gate (matches sc-mini's verification cascade):

    1. Witness check (cheap). Wrapper runs `witnessPolicy ws proposal r`
       — finite witnesses, computable. If it admits, we're done.

    2. Disjointness proof (definitive). On witness rejection, the LLM
       supplies a proof of `Disjoint proposal targetRule`; the wrapper
       declares `disjointProof : Disjoint proposal targetRule := <src>`.
       If Lean's kernel accepts the proof, `disjoint_policy_sound`
       gives us UnivSound for the resulting policy, hence
       conservative extension. Admit.

  Witness mode picks `targetRule`:
    - `base` mode: targetRule = stdRule  (proves CE-of-base)
    - `current` mode: targetRule = priors.foldl applyMod stdRule
      (proves CE-of-current — the strongest claim available)

  Dependencies: `lake` on PATH, project built (so `LeanBlack.Tower`
  resolves), invoked from a directory with the project's lakefile.
-/

import LeanBlack.Tower

namespace LeanBlack.Elab

inductive Result where
  | elabError (msg : String)
  | rejected
  /-- Proposal admitted by the cheap witness check. `witnessResult` is
      the `repr` of `applyMod proposal chained v args`, or `none`. -/
  | admittedByWitness (witnessResult : Option String)
  /-- Proposal admitted by an LLM-supplied, kernel-checked
      `Disjoint proposal targetRule` proof, after the witness check
      rejected. -/
  | admittedByProof (witnessResult : Option String)
  deriving Repr

def Result.isAdmitted : Result → Bool
  | .admittedByWitness _ | .admittedByProof _ => true
  | _ => false

instance : ToString Result where
  toString
    | .elabError m                  => s!"ELAB-ERROR: {m}"
    | .rejected                     => "REJECTED"
    | .admittedByWitness none       => "ADMITTED-WITNESS (witness produced none)"
    | .admittedByWitness (some r)   => s!"ADMITTED-WITNESS → {r}"
    | .admittedByProof   none       => "ADMITTED-PROOF (witness produced none)"
    | .admittedByProof   (some r)   => s!"ADMITTED-PROOF → {r}"

structure Config where
  witnessWrapperPath : String := "/tmp/leanblack-witness-check.lean"
  proofWrapperPath   : String := "/tmp/leanblack-proof-check.lean"
  /-- Working directory for the spawned `lake`. Must contain `lakefile.lean`. -/
  workingDir         : Option String := none

def defaultConfig : Config := {}

private def priorBlock (i : Nat) (propSrc witSrc : String) : String :=
  s!"def admitted_{i} : GuardedMod where\n{propSrc}\n\ndef admitted_{i}_wit : Val × List Val :=\n{witSrc}\n"

private def admittedListLit (n : Nat) : String :=
  let names := (List.range n).map (fun i => s!"admitted_{i}")
  "[" ++ String.intercalate ", " names ++ "]"

private def admittedWitnessFsts (n : Nat) : String :=
  let names := (List.range n).map (fun i => s!"admitted_{i}_wit.1")
  "[" ++ String.intercalate ", " names ++ "]"

/-- Common prelude: imports, prior defs, the new proposal + witness,
    and the chained-rule + target-rule definitions used by both wrappers. -/
private def buildPrelude
    (proposalSrc witnessSrc : String)
    (priors : List (String × String)) (currentMode : Bool) : String :=
  let priorDefs := priors.zipIdx.foldl
    (fun acc ⟨(p, w), i⟩ => acc ++ priorBlock i p w) ""
  let priorListLit := admittedListLit priors.length
  let target := if currentMode then "chained" else "stdRule"
  s!"import LeanBlack.Tower

{priorDefs}
def proposal : GuardedMod where
{proposalSrc}

def witness : Val × List Val :=
{witnessSrc}

def priors : List GuardedMod := {priorListLit}
def chained : ApplyRule := priors.foldl (fun r m => applyMod m r) stdRule
def targetRule : ApplyRule := {target}
"

private def buildWitnessWrapper
    (proposalSrc witnessSrc : String)
    (priors : List (String × String)) (currentMode : Bool) : String :=
  let prelude := buildPrelude proposalSrc witnessSrc priors currentMode
  let extra := if currentMode then admittedWitnessFsts priors.length else "[]"
  prelude ++ s!"
def policyWitnesses : List Val := stdWitnesses ++ {extra}

def main : IO Unit := do
  if witnessPolicy policyWitnesses proposal stdRule then
    let final := applyMod proposal chained
    let (v, args) := witness
    match final v args with
    | none   => IO.println \"ADMITTED-NONE\"
    | some r => IO.println (\"ADMITTED-RESULT \" ++ toString (repr r))
  else
    IO.println \"REJECTED\"
"

private def buildProofWrapper
    (proposalSrc witnessSrc proofSrc : String)
    (priors : List (String × String)) (currentMode : Bool) : String :=
  let prelude := buildPrelude proposalSrc witnessSrc priors currentMode
  prelude ++ s!"
-- Kernel-checked: if this elaborates, `disjoint_policy_sound` gives us
-- that any policy admitting this mod is UnivSound for `targetRule`.
def disjointProof : Disjoint proposal targetRule :=
{proofSrc}

def main : IO Unit := do
  let final := applyMod proposal chained
  let (v, args) := witness
  match final v args with
  | none   => IO.println \"ADMITTED-NONE\"
  | some r => IO.println (\"ADMITTED-RESULT \" ++ toString (repr r))
"

private def runWrapper (path : String) (workingDir : Option String) :
    IO (Bool × String × String) := do
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", path]
    cwd := workingDir
  }
  return (out.exitCode == 0, out.stdout, out.stderr)

private def parseWitnessOutcome (stdout : String) :
    Option (Bool × Option String) :=
  -- Returns (admitted?, witnessResult). None if output was unexpected.
  let lastLine := (stdout.trim.splitOn "\n").getLast?.getD ""
  if lastLine == "ADMITTED-NONE" then some (true, none)
  else if lastLine.startsWith "ADMITTED-RESULT " then
    some (true, some (lastLine.drop "ADMITTED-RESULT ".length))
  else if lastLine == "REJECTED" then some (false, none)
  else none

/-- Run the cheap witness check. Returns:
      `.elabError`         — proposal failed to elaborate;
      `.admittedByWitness` — witness check accepted;
      `.rejected`          — witness check refused (caller may retry with proof). -/
def checkProposalWitness (cfg : Config)
    (proposalSrc witnessSrc : String)
    (priors : List (String × String)) (currentMode : Bool)
    : IO Result := do
  IO.FS.writeFile cfg.witnessWrapperPath
    (buildWitnessWrapper proposalSrc witnessSrc priors currentMode)
  let (ok, stdout, stderr) ← runWrapper cfg.witnessWrapperPath cfg.workingDir
  if !ok then return .elabError (stdout ++ stderr).trim
  match parseWitnessOutcome stdout with
  | some (true, w) => return .admittedByWitness w
  | some (false, _) => return .rejected
  | none => return .elabError s!"unexpected witness-stage output:\n{stdout}"

/-- Run the definitive proof check. The LLM-supplied `proofSrc` is
    spliced as the body of `def disjointProof : Disjoint proposal targetRule`.
    Returns:
      `.elabError`        — proposal or proof failed to elaborate (kernel rejected);
      `.admittedByProof`  — proof type-checked, kernel admitted. -/
def checkProposalProof (cfg : Config)
    (proposalSrc witnessSrc proofSrc : String)
    (priors : List (String × String)) (currentMode : Bool)
    : IO Result := do
  IO.FS.writeFile cfg.proofWrapperPath
    (buildProofWrapper proposalSrc witnessSrc proofSrc priors currentMode)
  let (ok, stdout, stderr) ← runWrapper cfg.proofWrapperPath cfg.workingDir
  if !ok then return .elabError (stdout ++ stderr).trim
  let lastLine := (stdout.trim.splitOn "\n").getLast?.getD ""
  if lastLine == "ADMITTED-NONE" then return .admittedByProof none
  else if lastLine.startsWith "ADMITTED-RESULT " then
    return .admittedByProof (some (lastLine.drop "ADMITTED-RESULT ".length))
  else
    return .elabError s!"unexpected proof-stage output:\n{stdout}"

end LeanBlack.Elab

/-
  An LLM/Lean cascade over the reflective tower's gate:
    cheap witness check first, then (on rejection) an LLM-supplied,
    kernel-checked disjointness proof.

  Each round:
    1. Prompt Bedrock for a PROPOSAL (where-block body) + WITNESS
       (Val × List Val term that exercises the proposal).
    2. Run `checkProposalWitness`.
    3. On `.admittedByWitness`: done — admitted by the cheap path.
    4. On `.elabError`: retry the proposal up to `maxElabRetries`.
    5. On `.rejected`: ask the LLM for a PROOF of `Disjoint proposal targetRule`;
       run `checkProposalProof`. Admit if the kernel accepts the proof,
       reject if it doesn't (after `maxProofRetries` retries).
-/

import LeanBlack.Bedrock
import LeanBlack.Elab

namespace LeanBlack.Runner

structure RoundResult where
  proposalSrc : String
  witnessSrc  : String
  proofSrc    : Option String
  outcome     : LeanBlack.Elab.Result

/-- Which target rule the gate is checking disjointness against. -/
inductive Mode where
  | base     -- targetRule = stdRule (CE-of-base)
  | current  -- targetRule = priors composed with stdRule (CE-of-current)
  deriving Repr, BEq

instance : ToString Mode where
  toString | .base => "base" | .current => "current"

structure Config where
  maxElabRetries  : Nat := 1
  maxProofRetries : Nat := 1
  mode            : Mode := .base

def defaultConfig : Config := {}

def Mode.targetDescription : Mode → String
  | .base    => "stdRule (the base interpreter)"
  | .current => "the current chained rule (stdRule extended by all previously admitted mods)"

/-- Compose the proposer prompt for the PROPOSAL+WITNESS round. -/
def buildProposalPrompt
    (admitted : List String) (mode : Mode)
    (retry : Option (String × String × String) := none) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\nPreviously admitted (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
  let retrySection := match retry with
    | none => ""
    | some (prevProp, prevWit, err) =>
      s!"\nYour previous attempt was rejected by Lean.\n\nPROPOSAL:\n{prevProp}\n\nWITNESS:\n{prevWit}\n\nLean's diagnostic:\n{err}\n\nPlease produce a corrected version.\n"
  s!"You are proposing a new primitive operation for a reflective tower.

A `GuardedMod` is a Lean 4 record:

  guard   : Val → Bool                           -- when does it apply?
  handler : Val → List Val → Option Val          -- what does it do?

`Val` is the inductive:

  | num     : Int → Val
  | bool    : Bool → Val
  | closure : List String → Expr → List (String × Val) → Val
  | prim    : String → Val

Constraints (the cheap witness gate enforces these against
{mode.targetDescription}):
  - guard MUST NOT fire on `.prim \"+\"`, `.prim \"-\"`, `.prim \"*\"`
  - guard MUST NOT fire on `.closure _ _ _`
  - The term must elaborate under `import LeanBlack.Tower` only.
{admittedSection}{retrySection}
Output format: TWO sections, each with a header line in ALL CAPS.

PROPOSAL:
  <indented two-space `where`-block field bindings: guard and handler>

WITNESS:
  <a Lean 4 term of type `Val × List Val` that exercises your proposal>

No markdown fences. No commentary. Example:

PROPOSAL:
  guard v := match v with | .num _ => true | _ => false
  handler v args := match v, args with
    | .num n, [.num m] => some (.num (n + m))
    | _, _ => none

WITNESS:
  (.num 2, [.num 3])
"

/-- Compose the proof-stage prompt: witness check rejected, please supply
    a `Disjoint proposal targetRule` proof. -/
def buildProofPrompt
    (mode : Mode) (proposalSrc witnessSrc : String)
    (retry : Option (String × String) := none) : String :=
  let retrySection := match retry with
    | none => ""
    | some (prevProof, err) =>
      s!"\nYour previous proof was rejected by Lean.\n\nPROOF:\n{prevProof}\n\nLean's diagnostic:\n{err}\n\nPlease produce a corrected proof.\n"
  s!"Your proposal passed elaboration but failed the cheap witness check.

Your proposal:

PROPOSAL:
{proposalSrc}

WITNESS:
{witnessSrc}

To install it anyway, supply a Lean 4 proof of:

  Disjoint proposal targetRule

where `targetRule` is {mode.targetDescription}, and `Disjoint` is:

  def Disjoint (m : GuardedMod) (r : ApplyRule) : Prop :=
    ∀ v args, m.guard v = true → r v args = none

Your proof will be spliced as the body of:

  def disjointProof : Disjoint proposal targetRule := <YOUR PROOF>

so it should be a single Lean 4 expression of that type. The simplest
shape is a `fun v args hg => …` term that case-analyses `v` and shows
that whenever the guard fires, the target rule returns `none`.
{retrySection}
Output format: ONE section.

PROOF:
  <Lean 4 term>

No markdown fences. No commentary."

/-- Pull a section's body out of the LLM's reply. Sections are introduced
    by an ALL-CAPS header line ending in ':'. -/
def extractSection (header : String) (raw : String) : String :=
  let s := raw.replace "```lean" "" |>.replace "```lean4" "" |>.replace "```" ""
  let lines := s.splitOn "\n"
  let rec collect (taking : Bool) (acc : List String) : List String → List String
    | [] => acc.reverse
    | l :: rest =>
      if l.trim == header then
        collect true acc rest
      else if taking && l.trim.endsWith ":" && (l.trim.toList.all (fun c => c.isUpper || c == ':' || c == ' ')) then
        acc.reverse
      else if taking then
        collect true (l :: acc) rest
      else
        collect false acc rest
  String.intercalate "\n" (collect false [] lines) |>.trim

/-- Add a missing leading indent on the first non-empty line, since LLMs
    commonly trim that, breaking Lean's indent-sensitive `where` blocks. -/
def fixFirstLineIndent (src : String) : String :=
  match src.splitOn "\n" with
  | first :: rest =>
    let firstNeedsFix := !first.trim.isEmpty && !first.startsWith " "
    let restHasIndent := rest.any (fun l => l.startsWith "  ")
    if firstNeedsFix && restHasIndent then
      String.intercalate "\n" (("  " ++ first) :: rest)
    else src
  | _ => src

/-- The proof stage: ask LLM for a Disjoint proof, kernel-check it,
    optionally retry with the diagnostic on failure. -/
private def runProofStage
    (bcfg : LeanBlack.Bedrock.Config) (ecfg : LeanBlack.Elab.Config)
    (rcfg : Config) (priors : List (String × String))
    (proposalSrc witnessSrc : String) :
    IO (Option String × LeanBlack.Elab.Result) := do
  let currentMode := rcfg.mode == .current
  let rec attempt (retry : Option (String × String)) (remaining : Nat) :
      IO (Option String × LeanBlack.Elab.Result) := do
    let prompt := buildProofPrompt rcfg.mode proposalSrc witnessSrc retry
    match ← LeanBlack.Bedrock.invoke bcfg prompt with
    | .error e =>
      IO.eprintln s!"Bedrock error during proof stage: {e}"
      return (none, .rejected)
    | .ok rawResponse =>
      let proofSrc := (extractSection "PROOF:" rawResponse).trim
      IO.println "--- LLM proof ---"
      IO.println proofSrc
      let outcome ← LeanBlack.Elab.checkProposalProof
        ecfg proposalSrc witnessSrc proofSrc priors currentMode
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(proof rejected by Lean; retrying, {remaining} left)"
          attempt (some (proofSrc, msg)) (remaining - 1)
        else
          return (some proofSrc, .rejected)
      | _ => return (some proofSrc, outcome)
  attempt none rcfg.maxProofRetries

/-- Run one LLM proposal round through the cascade: witness check, then
    on rejection a kernel-checked disjointness proof. -/
def runOneRound
    (bcfg : LeanBlack.Bedrock.Config) (ecfg : LeanBlack.Elab.Config)
    (rcfg : Config) (priors : List (String × String))
    : IO (Option RoundResult) := do
  let admittedProposals := priors.map Prod.fst
  let currentMode := rcfg.mode == .current
  let rec proposalAttempt (retry : Option (String × String × String))
                          (remaining : Nat) : IO (Option RoundResult) := do
    let prompt := buildProposalPrompt admittedProposals rcfg.mode retry
    match ← LeanBlack.Bedrock.invoke bcfg prompt with
    | .error e =>
      IO.eprintln s!"Bedrock error: {e}"
      return none
    | .ok rawResponse =>
      let proposalSrc := fixFirstLineIndent (extractSection "PROPOSAL:" rawResponse)
      let witnessSrc  := (extractSection "WITNESS:" rawResponse).trim
      IO.println "--- LLM proposed ---"
      IO.println s!"PROPOSAL:\n{proposalSrc}"
      IO.println s!"WITNESS:\n{witnessSrc}"
      let witnessOutcome ← LeanBlack.Elab.checkProposalWitness
        ecfg proposalSrc witnessSrc priors currentMode
      match witnessOutcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying proposal, {remaining} left)"
          proposalAttempt (some (proposalSrc, witnessSrc, msg)) (remaining - 1)
        else
          return some ⟨proposalSrc, witnessSrc, none, witnessOutcome⟩
      | .admittedByWitness _ =>
        return some ⟨proposalSrc, witnessSrc, none, witnessOutcome⟩
      | .rejected =>
        IO.println "(witness check rejected; asking LLM for disjointness proof)"
        let (proofSrc, outcome) ← runProofStage bcfg ecfg rcfg priors proposalSrc witnessSrc
        return some ⟨proposalSrc, witnessSrc, proofSrc, outcome⟩
      | other => return some ⟨proposalSrc, witnessSrc, none, other⟩
  proposalAttempt none rcfg.maxElabRetries

end LeanBlack.Runner

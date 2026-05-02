/-
  An LLM/Lean loop over the reflective tower's gate, with witness
  evaluation and retry on elaboration error.

  Each round:
    1. Prompt Bedrock for a PROPOSAL (where-block body) plus a WITNESS
       (Val × List Val term that exercises the proposal).
    2. Parse out both sections.
    3. Send through `LeanBlack.Elab.checkProposal` with the running list
       of previously-admitted proposals as priors. The wrapper folds the
       priors and the new proposal into a chained rule and evaluates
       the witness against it.
    4. Classify: elabError | rejected | admitted (with witness result).
    5. On elabError, optionally re-prompt with Lean's diagnostic and
       retry up to `maxRetries`.
-/

import LeanBlack.Bedrock
import LeanBlack.Elab

namespace LeanBlack.Runner

structure RoundResult where
  proposalSrc : String
  witnessSrc  : String
  outcome     : LeanBlack.Elab.Result

structure Config where
  maxRetries : Nat := 1

def defaultConfig : Config := {}

/-- Compose the proposer prompt. Optionally include the prior attempt
    and Lean's diagnostic for retry rounds. -/
def buildPrompt
    (admitted : List String) (retry : Option (String × String × String) := none)
    : String :=
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

Constraints (the policy will reject violations):
  - guard MUST NOT fire on `.prim \"+\"`, `.prim \"-\"`, `.prim \"*\"`
  - guard MUST NOT fire on `.closure _ _ _`
  - The term must elaborate under `import LeanBlack.Tower` only.
{admittedSection}{retrySection}
Output format: TWO sections, each with a header line in ALL CAPS.

PROPOSAL:
  <indented two-space `where`-block field bindings: guard and handler>

WITNESS:
  <a Lean 4 term of type `Val × List Val` that exercises your proposal —
   the value to apply and its argument list. The wrapper will compute
   `applyMod proposal stdRule v args` and report the result.>

No markdown fences. No commentary. Example:

PROPOSAL:
  guard v := match v with | .num _ => true | _ => false
  handler v args := match v, args with
    | .num n, [.num m] => some (.num (n + m))
    | _, _ => none

WITNESS:
  (.num 2, [.num 3])
"

/-- Pull a section's body out of the LLM's reply. Sections are introduced
    by an ALL-CAPS header line ending in ':'. The body runs from the
    line after the header until the next header or end-of-text. -/
def extractSection (header : String) (raw : String) : String :=
  let s := raw.replace "```lean" "" |>.replace "```lean4" "" |>.replace "```" ""
  let lines := s.splitOn "\n"
  let rec collect (taking : Bool) (acc : List String) : List String → List String
    | [] => acc.reverse
    | l :: rest =>
      if l.trim == header then
        collect true acc rest
      else if taking && l.trim.endsWith ":" && (l.trim.toList.all (fun c => c.isUpper || c == ':' || c == ' ')) then
        -- next ALL-CAPS header — stop
        acc.reverse
      else if taking then
        collect true (l :: acc) rest
      else
        collect false acc rest
  String.intercalate "\n" (collect false [] lines) |>.trim |> trimTrailingFences
where
  trimTrailingFences (s : String) : String := s.trim

/-- LLMs commonly trim leading whitespace from the first line of their
    response, which breaks Lean's indent-sensitive `where` block. If the
    first non-empty line lacks indent but later lines have it, prepend
    two spaces to the first line. -/
def fixFirstLineIndent (src : String) : String :=
  match src.splitOn "\n" with
  | first :: rest =>
    let firstNeedsFix := !first.trim.isEmpty && !first.startsWith " "
    let restHasIndent := rest.any (fun l => l.startsWith "  ")
    if firstNeedsFix && restHasIndent then
      String.intercalate "\n" (("  " ++ first) :: rest)
    else src
  | _ => src

/-- Run one LLM proposal round, with retry on elaboration error. -/
def runOneRound
    (bcfg : LeanBlack.Bedrock.Config) (ecfg : LeanBlack.Elab.Config)
    (rcfg : Config) (admitted : List String) : IO (Option RoundResult) := do
  let rec attempt (retry : Option (String × String × String))
                  (remaining : Nat) : IO (Option RoundResult) := do
    let prompt := buildPrompt admitted retry
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
      let outcome ← LeanBlack.Elab.checkProposal ecfg proposalSrc witnessSrc admitted
      match outcome with
      | .elabError msg =>
        if remaining > 0 then
          IO.println s!"(elab error; retrying, {remaining} left)"
          attempt (some (proposalSrc, witnessSrc, msg)) (remaining - 1)
        else
          return some ⟨proposalSrc, witnessSrc, outcome⟩
      | _ => return some ⟨proposalSrc, witnessSrc, outcome⟩
  attempt none rcfg.maxRetries

end LeanBlack.Runner

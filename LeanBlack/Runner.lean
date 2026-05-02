/-
  An LLM/Lean loop over the reflective tower's gate.

  Each round:
    1. Prompt Bedrock for a `GuardedMod` term (Lean source).
    2. Extract the term (handle markdown fences if the LLM uses them).
    3. Send through `LeanBlack.Elab.checkProposal`, which spawns a
       fresh `lake env lean --run` over a wrapper that imports Tower,
       defines `proposal : GuardedMod := <src>`, and runs the
       `witnessPolicy stdWitnesses proposal stdRule` policy gate.
    4. Classify: elabError | rejected | admitted.

  Admitted proposal sources accumulate across rounds and are fed back
  into the next prompt so the LLM can vary its proposals. The tower's
  evaluation state is not persisted across rounds for this demo;
  `witnessPolicy` is rule-independent, so each round's policy verdict
  is independent of accumulated mods.
-/

import LeanBlack.Bedrock
import LeanBlack.Elab

namespace LeanBlack.Runner

structure RoundResult where
  proposalSrc : String
  outcome     : LeanBlack.Elab.Result

/-- Compose the proposer prompt. -/
def buildPrompt (admitted : List String) : String :=
  let admittedSection := if admitted.isEmpty then "" else
    "\nPreviously admitted (don't propose duplicates):\n" ++
    String.intercalate "\n---\n" admitted ++ "\n"
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
{admittedSection}
Output format: emit ONLY two field bindings, indented with two spaces,
that will be spliced into a `def proposal : GuardedMod where` block.
No markdown fences. No commentary. No `def` line. No `where` keyword.

Example output (this exact shape):

  guard v := match v with | .num _ => true | _ => false
  handler v args := match v, args with
    | .num n, [] => some (.num (n + 1))
    | _, _ => none
"

/-- Pull a Lean term out of the LLM's reply. Tolerates ```​lean … ```​
    and stray prose by extracting the first fenced block if present. -/
def extractTerm (raw : String) : String :=
  let s := raw.trim
  let parts := s.splitOn "```"
  match parts with
  | _ :: inner :: _ =>
    let inner := inner.trim
    -- Strip optional "lean" / "lean4" language tag on the first line
    let stripped :=
      if inner.startsWith "lean4" then (inner.drop 5).trim
      else if inner.startsWith "lean" then (inner.drop 4).trim
      else inner
    stripped
  | _ => s

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

/-- Run one LLM proposal round. Returns the proposal source and verdict,
    or `none` if the Bedrock call itself failed. -/
def runOneRound
    (bcfg : LeanBlack.Bedrock.Config) (ecfg : LeanBlack.Elab.Config)
    (admitted : List String) : IO (Option RoundResult) := do
  let prompt := buildPrompt admitted
  match ← LeanBlack.Bedrock.invoke bcfg prompt with
  | .error e =>
    IO.eprintln s!"Bedrock error: {e}"
    return none
  | .ok rawResponse =>
    let proposalSrc := fixFirstLineIndent (extractTerm rawResponse)
    IO.println "--- LLM proposed ---"
    IO.println proposalSrc
    let outcome ← LeanBlack.Elab.checkProposal ecfg proposalSrc
    return some ⟨proposalSrc, outcome⟩

end LeanBlack.Runner

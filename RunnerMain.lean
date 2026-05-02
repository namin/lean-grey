import LeanBlack.Runner

/-- Usage: lake exe runner [N] [base|current]
    N defaults to 3, mode defaults to base. -/
def main (args : List String) : IO Unit := do
  let nRounds : Nat := args.head?.bind (·.toNat?) |>.getD 3
  let mode : LeanBlack.Runner.Mode := match args[1]? with
    | some "current" => .current
    | _              => .base
  IO.println s!"runner: {nRounds} rounds, mode = {mode}"
  let bcfg : LeanBlack.Bedrock.Config := {}
  let ecfg : LeanBlack.Elab.Config := {}
  let rcfg : LeanBlack.Runner.Config := { mode }
  let mut priors : List (String × String) := []  -- (proposalSrc, witnessSrc)
  let mut log : List LeanBlack.Runner.RoundResult := []
  for i in [0:nRounds] do
    IO.println s!"\n========== ROUND {i+1}/{nRounds} =========="
    match ← LeanBlack.Runner.runOneRound bcfg ecfg rcfg priors with
    | none => IO.eprintln "(round skipped: Bedrock error)"
    | some r =>
      IO.println s!"VERDICT: {r.outcome}"
      log := log ++ [r]
      match r.outcome with
      | .admitted _ => priors := priors ++ [(r.proposalSrc, r.witnessSrc)]
      | _ => pure ()
  IO.println "\n========== SUMMARY =========="
  IO.println s!"Mode:         {mode}"
  IO.println s!"Total rounds: {log.length}"
  IO.println s!"Admitted:     {priors.length}"
  let nRej := log.filter (fun r => match r.outcome with | .rejected => true | _ => false) |>.length
  let nErr := log.filter (fun r => match r.outcome with | .elabError _ => true | _ => false) |>.length
  IO.println s!"Rejected:     {nRej}"
  IO.println s!"Elab errors:  {nErr}"

import LeanBlack.Runner

def main (args : List String) : IO Unit := do
  let nRounds : Nat := args.head?.bind (·.toNat?) |>.getD 3
  let bcfg : LeanBlack.Bedrock.Config := {}
  let ecfg : LeanBlack.Elab.Config := {}
  let rcfg : LeanBlack.Runner.Config := {}
  let mut admitted : List String := []
  let mut log : List LeanBlack.Runner.RoundResult := []
  for i in [0:nRounds] do
    IO.println s!"\n========== ROUND {i+1}/{nRounds} =========="
    match ← LeanBlack.Runner.runOneRound bcfg ecfg rcfg admitted with
    | none => IO.eprintln "(round skipped: Bedrock error)"
    | some r =>
      IO.println s!"VERDICT: {r.outcome}"
      log := log ++ [r]
      match r.outcome with
      | .admitted _ => admitted := admitted ++ [r.proposalSrc]
      | _ => pure ()
  IO.println "\n========== SUMMARY =========="
  IO.println s!"Total rounds: {log.length}"
  IO.println s!"Admitted:     {admitted.length}"
  let nRej := log.filter (fun r => match r.outcome with | .rejected => true | _ => false) |>.length
  let nErr := log.filter (fun r => match r.outcome with | .elabError _ => true | _ => false) |>.length
  IO.println s!"Rejected:     {nRej}"
  IO.println s!"Elab errors:  {nErr}"

import LeanBlack.Elab

def main : IO Unit := do
  let cfg : LeanBlack.Elab.Config := {}
  -- Each case is (label, proposal `where`-body, witness term).
  let cases : List (String × String × String) := [
    -- Admitted: multnMod-like, witness exercises numbers as multiplication.
    ("multnMod-like (admitted)",
      "  guard := multnMod.guard\n  handler := multnMod.handler",
      "(.num 2, [.num 3, .num 4])"),
    -- Rejected: guard fires on .prim, witness irrelevant since policy rejects.
    ("override prim (rejected)",
      "  guard v := match v with | .prim _ => true | _ => false\n  handler _ _ := some (.num 0)",
      "(.prim \"+\", [.num 1, .num 2])"),
    -- Elab error: unknown identifier.
    ("nonsense (elab error)", "this_is_not_a_guarded_mod", "(.num 0, [])")
  ]
  for (label, propSrc, witSrc) in cases do
    IO.println s!"\n=== {label} ==="
    let r ← LeanBlack.Elab.checkProposal cfg propSrc witSrc []
    IO.println s!"-> {r}"

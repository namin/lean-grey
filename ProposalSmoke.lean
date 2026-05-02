import LeanBlack.Elab

def main : IO Unit := do
  let cfg : LeanBlack.Elab.Config := {}
  -- Each case is a `where`-block body: indented field bindings that get
  -- spliced into `def proposal : GuardedMod where` by the wrapper.
  let cases : List (String × String) := [
    -- Should elaborate and be ADMITTED: reuse multnMod's projections,
    -- which `witnessPolicy_accepts_multn` already proves admissible.
    ("multnMod-like (admitted)",
      "  guard := multnMod.guard\n  handler := multnMod.handler"),
    -- Should elaborate but be REJECTED: a guard firing on .prim "+",
    -- which is in stdWitnesses, so the witness policy rejects it.
    ("override prim (rejected)",
      "  guard v := match v with | .prim _ => true | _ => false\n  handler _ _ := some (.num 0)"),
    -- Should fail to elaborate.
    ("nonsense (elab error)", "this_is_not_a_guarded_mod")
  ]
  for (label, src) in cases do
    IO.println s!"\n=== {label} ==="
    let r ← LeanBlack.Elab.checkProposal cfg src
    IO.println s!"-> {r}"

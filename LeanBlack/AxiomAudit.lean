import LeanBlack.Tower

/-!
# Axiom audit

Machine-witnesses that lean-grey's headline results rest only on the Lean kernel
plus the standard classical axioms — crucially, **no `Lean.ofReduceBool`** (the
axiom `native_decide` injects to trust the compiler instead of the kernel) and no
`sorryAx`. Each `#guard_msgs in #print axioms …` pins the exact footprint, so the
build fails the moment any audited theorem acquires a new axiom.
-/

/-- info: 'install_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms install_safe

/-- info: 'installPolicy_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms installPolicy_safe

/-- info: 'eval_tower_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_tower_conservative

/-- info: 'badMod_not_conservative' depends on axioms: [propext] -/
#guard_msgs in
#print axioms badMod_not_conservative

/-- info: 'witnessPolicy_accepts_multn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms witnessPolicy_accepts_multn

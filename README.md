# lean-black

A formalization of Black's reflective tower in Lean 4, with verified reflection.

## What Black is

Black (Asai, Matsuoka, Yonezawa 1996) is a reflective tower of interpreters. The key features:

1. **The evaluator's components are data.** `base-eval`, `base-apply`, and all other evaluator functions are bindings in the meta-environment — values that programs can access and modify.

2. **EM (exec-at-metalevel).** A program at level N can execute code at level N+1. At level N+1, the evaluator components for level N are ordinary bindings that can be inspected and `set!`'d.

3. **The tower is infinite.** EM can be nested: `(EM (EM ...))` goes up two levels. Each level interprets the level below. Levels are created lazily — the tower extends on demand.

4. **Modifications take causal effect.** When level N+1 modifies `base-apply` for level N, future evaluation at level N uses the new `base-apply`. This is Smith's "causal connection" — the representation IS the thing.

## What a real tower formalization needs

### Level structure

A tower is an infinite sequence of levels. Each level has:
- An **environment** (meta-env) containing the evaluator components for the level below
- An **apply rule** and **eval function** that interpret the level below
- The ability to **modify** the level below's components via `set!` on its own environment

Level 0 is the user program. Level 1 is the meta-level that interprets level 0. Level 2 interprets level 1. And so on.

### EM as level-shifting

`(EM expr)` at level N:
1. Shifts up to level N+1
2. Evaluates `expr` in level N+1's environment (which contains level N's evaluator components as bindings)
3. Any modifications to those bindings take effect at level N
4. Returns to level N with the result

Nested EM: `(EM (EM expr))` at level 0 evaluates `expr` at level 2, which can modify level 1's components (including how level 1 governs level 0).

### Governance as a reflective artifact

In the current formalization, the governance policy is a fixed Lean function. In a real tower:
- The governance policy for level N is a component at level N+1
- Level N+2 can modify it via EM
- The policy is itself subject to reflection — the tower governs its own governance

This is the deep point: the verification gate is not external scaffolding. It's inside the tower, subject to the same reflective operations as everything else.

### The meta-continuation

Black uses meta-continuations (lazy streams) to connect levels. Each level's continuation is paired with the meta-environment and meta-continuation of the level above. This is what makes the tower finite in implementation but infinite in principle — new levels are created on demand when EM is invoked.

## What we have now

`LeanBlack/Tower.lean` — a multi-level reflective tower with EM, reflective governance, and proved safety theorems. Fully proved, no sorry.

### Tower structure

Each level has an apply rule AND a governance policy, both part of the tower state:

```
structure LevelState where
  rule : ApplyRule
  policy : Policy

abbrev TowerState := Nat → LevelState
```

Three expression forms for reflection:
- `(em body)` — shift up one level and evaluate body. Nested EM works.
- `(install n)` — install rule modification #n at this level, governed by this level's policy. Affects the level below (which uses this level's rule for apply dispatch).
- `(installPolicy n)` — replace this level's policy from the policy table.

### Theorems (all fully proved)

**Tower safety** (`eval_tower_conservative`): If `SafeEvolution` holds (all policies in tower and table are universally sound), then evaluating any program — with EM, install, and installPolicy at any depth — preserves conservative extension across the entire tower AND preserves `SafeEvolution`.

```
eval_tower_conservative:
  SafeEvolution ptable tower →
  eval mods ptable fuel level exp env tower = some (v, tower') →
  TowerConservative tower tower' ∧ SafeEvolution ptable tower'
```

**Governance coherence** (`installPolicy_safe`): Replacing a level's policy with a universally sound policy preserves `SafeEvolution`. The tower's governance is self-sustaining under reflective modification.

**Install safety** (`install_safe`): Installing a rule modification that passes a universally sound policy preserves `SafeEvolution`. Universal soundness (sound for any rule) is the key: it survives rule changes.

### Smoke tests

```
(+ 1 2)                                    => 3     -- basic eval
(2 3 4)                                    => none  -- no multn
(em (install 0)); (2 3 4)                  => 24    -- EM installs multn
(em (install 0)); (+ 1 2)                  => 3     -- old behavior preserved
(em (em (install 0)))                      => true  -- nested EM, level 2
-- Reflective governance:
start with rejectAll;
(em (installPolicy 0));                              -- replace policy with acceptAll
(em (install 0)); (2 3 4)                  => 24    -- now multn installs
-- Without policy change:
(em (install 0)); (2 3 4)                  => rejected
```

### Necessity of external governance (`safeEvolution_necessary`)
The converse of tower safety: without `SafeEvolution`, there exist programs that break conservative extension. A concrete counterexample is constructed — `badMod` (overwrites primitives with 0) is installed via `(em (install 0))` under an `acceptAll` policy. Supporting lemmas: `badMod_not_conservative`, `acceptAll_not_univSound`.

This is necessary conditions, not incompleteness. It shows the external assumption can't be dropped, not that it can't be verified from within.

### Connection to Black's assume.blk
The disjoint-guard policy from `assume.blk` is formalized as `witnessPolicy` and proved sound (`disjoint_policy_sound`). The concrete instance: `multn_disjoint_std` proves multn's guard is disjoint from stdRule. The gap between the witness-based check (finite, computable) and true disjointness (universal, non-computable) is the assurance lattice from the keynote.

## Open

### The Gödelian limit (not yet formalized)
The real incompleteness result would be: no program in the tower can verify `SafeEvolution` for itself. This requires a notion of "what programs can verify" that the current formalization doesn't have. Level N can verify modifications to level N-1, but not to itself — this parallels iterated reflection principles in logic, but making it a theorem needs more machinery.

### Richer modifications
Currently restricted to the guard+handler pattern. Black allows arbitrary code at the meta-level.

### Meta-continuations
A coinductive formalization (mirroring Black's lazy meta-continuation streams) would be more faithful than fuel.

### Fixpoint semantics
Define the tower semantics as a fixpoint of the "interpret the level below" operation (following Wand-Friedman). Connects to domain theory and is perhaps most natural for a LICS audience.

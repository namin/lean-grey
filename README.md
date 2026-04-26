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

`LeanBlack/Tower.lean` — a single-level evaluator with:
- An apply rule parameterized and modifiable via EM
- A governance policy (fixed, external) that gates modifications
- A theorem: governed EM can only produce conservative extensions of the original rule

This is one level of reflection, not a tower. The governance policy can't be reflectively modified. There is no level-shifting.

## What the real formalization would prove

### Tower safety
If governance at every level is sound, and governance is only modified through sound governance at the level above, then the tower as a whole preserves conservative extension. Self-modification at any level, to any depth, cannot break existing behavior — as long as every modification passes through a sound gate.

### Governance coherence
If level N+2 modifies level N+1's governance policy, the new policy is still sound (because the modification was itself governed). The tower's governance is self-sustaining.

### The Gödelian limit
Level N can verify modifications to level N-1, but not to itself. The tower cannot verify its own base level's governance without going up a level. This is the computational analog of Gödel's incompleteness: each level can prove the soundness of the level below, but not its own.

## Approach

The formalization could proceed in two ways:

**Indexed family.** Define `Level : Nat → Type` with `eval : Level n → Expr → Env → Option Val` and `em : Level n → Level (n+1)`. The tower is the family. Theorems are quantified over level indices.

**Coinductive / stream.** Define the tower as a coinductive stream of level states, mirroring Black's lazy meta-continuation. Levels are produced on demand. This is closer to the implementation but harder to reason about in Lean.

**Fixpoint.** Define the tower semantics as a fixpoint of the "interpret the level below" operation (following Wand-Friedman). The tower is the least fixpoint. This connects to domain theory and is perhaps most natural for a LICS audience.

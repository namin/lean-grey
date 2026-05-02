# lean-grey

A formalization inspired by the Black reflective tower in Lean 4, with verified reflection.

## What Black is

[Black](https://github.com/readevalprintlove/black) (Asai, Matsuoka, Yonezawa 1996) is a reflective tower of interpreters. The key features:

1. **The evaluator's components are data.** `base-eval`, `base-apply`, and all other evaluator functions are bindings in the meta-environment — values that programs can access and modify.

2. **EM (exec-at-metalevel).** A program at level N can execute code at level N+1. At level N+1, the evaluator components for level N are ordinary bindings that can be inspected and `set!`'d.

3. **The tower is infinite.** EM can be nested: `(EM (EM ...))` goes up two levels. Each level interprets the level below. Levels are created lazily — the tower extends on demand.

4. **Modifications take causal effect.** When level N+1 modifies `base-apply` for level N, future evaluation at level N uses the new `base-apply`. This is Smith's "causal connection" — the representation IS the thing.

## What a real tower formalization needs

### Level structure ✓

A tower is an infinite sequence of levels. Each level has:
- An **environment** (meta-env) containing the evaluator components for the level below
- An **apply rule** and **eval function** that interpret the level below
- The ability to **modify** the level below's components via `set!` on its own environment

Level 0 is the user program. Level 1 is the meta-level that interprets level 0. Level 2 interprets level 1. And so on.

### EM as level-shifting ✓

`(EM expr)` at level N:
1. Shifts up to level N+1
2. Evaluates `expr` in level N+1's environment (which contains level N's evaluator components as bindings)
3. Any modifications to those bindings take effect at level N
4. Returns to level N with the result

Nested EM: `(EM (EM expr))` at level 0 evaluates `expr` at level 2, which can modify level 1's components (including how level 1 governs level 0).

### Governance as a reflective artifact ✓

The governance policy at each level is part of `LevelState` and modifiable via `(installPolicy n)` through EM. Level N+2 can modify level N+1's policy. The tower governs its own governance. The governance coherence theorem (`installPolicy_safe`) proves `SafeEvolution` is maintained.

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

**Parametric soundness** (`Policy.SoundFor`, `Policy.UnivSoundFor`): the existing `Policy.Sound` / `Policy.UnivSound` are the `ConservativeExt` instantiation of more general predicates parameterized over a property `P : ApplyRule → ApplyRule → Prop`. A library of policies, each statically proved sound for its property (CE-of-base, CE-of-current, termination, type safety, etc.), can sit in the same architecture; the choice of policy is what specifies which safety claim is being made.

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

### Connection to [Black's assume.blk](https://github.com/namin/black/blob/play-assume/ASSUME.md)
The disjoint-guard policy from [`assume.blk`](https://github.com/namin/black/blob/play-assume/examples/assume.blk) is formalized as `witnessPolicy` and proved sound (`disjoint_policy_sound`). The concrete instance: `multn_disjoint_std` proves multn's guard is disjoint from stdRule. The gap between the witness-based check (finite, computable) and true disjointness (universal, non-computable) is the assurance lattice.

## LLM-driven gate

A small loop in which Claude (via AWS Bedrock) proposes a `GuardedMod` in Lean source, and a two-stage cascade decides whether to admit it: a cheap witness check first; on rejection, an LLM-supplied, kernel-checked `Disjoint` proof.

- **`LeanBlack/Bedrock.lean`** — `invoke : Config → String → IO (Except String String)`, wrapping `aws bedrock-runtime invoke-model`. Reads AWS credentials from the standard chain (env vars or `~/.aws/credentials`); defaults to `us-east-1` and `us.anthropic.claude-sonnet-4-6`.
- **`LeanBlack/Elab.lean`** — two stages.
  - `checkProposalWitness` writes a wrapper that splices the proposal, witness, and prior admits, then runs `witnessPolicy ws proposal stdRule` in `main`. Returns `elabError | admittedByWitness | rejected`. Cheap, finite, computable.
  - `checkProposalProof` writes a wrapper that adds `def disjointProof : Disjoint proposal targetRule := <LLM proof source>` — if the kernel accepts the proof, `disjoint_policy_sound` gives us `UnivSound` for the resulting policy, hence conservative extension. Returns `elabError | admittedByProof`.
- **`LeanBlack/Runner.lean`** — orchestrates the cascade. Each round: prompt for `PROPOSAL` + `WITNESS`, run the witness check; on `rejected`, re-prompt for `PROOF` of `Disjoint proposal targetRule`, run the proof check; classify. Elaboration retries up to `maxElabRetries` (default 1) for the proposal stage and `maxProofRetries` (default 1) for the proof stage. On `elabError` the runner feeds Lean's diagnostic into the retry prompt.

### Running

Prerequisites: `aws` CLI on PATH with Bedrock-enabled credentials, and the project built (`lake build`).

```bash
lake exe bedrock-smoke               # one-shot round trip ("READY")
lake exe proposal-smoke              # exercise admitted / rejected / elab-error
                                     # on three hardcoded proposals
lake exe runner [N] [base|current]   # N rounds; mode picks the target rule.
                                     # default: 3 rounds, base mode.
```

The two modes pick the rule the proof must show disjointness from:

- **base** uses `targetRule = stdRule`. Witness check uses `stdWitnesses`. Proof obligation is `Disjoint proposal stdRule` (CE-of-base).
- **current** uses `targetRule = priors.foldl applyMod stdRule`. Witness check extends `stdWitnesses` with prior witness values. Proof obligation is `Disjoint proposal currentRule` (CE-of-current — the strongest claim available at this point in the run).

A typical 3-round contrast:

```
base:    3 proposals → 3 admitted by witness         (no proof stage triggered)
current: 3 proposals → 2 admitted by witness, 1 rejected
                       (round 3 num-handler fails witness; LLM-supplied
                        Disjoint proof also fails because the property
                        genuinely doesn't hold — the proposal really does
                        overlap with round 2's mod)
```

The current-mode rejection is the safety property working: the proposal isn't disjoint from the current rule, so no proof of `Disjoint proposal currentRule` can exist, and the kernel correctly refuses to admit one.

On admit, the wrapper computes `applyMod proposal (priors.foldl applyMod stdRule) v args` for the LLM's `(v, args)` witness and prints the value's `repr` — so each round shows what the just-admitted mod actually does.

### Scope and limits

The cascade is sound by construction: `admittedByWitness` invokes `witnessPolicy` (proven sound for `stdRule` via `disjoint_policy_sound`), and `admittedByProof` invokes the kernel on a Lean term of type `Disjoint proposal targetRule`. The LLM's role is constrained to the proposer side of the LCF discipline.

Remaining caveats:

- Retry attempts overwrite the verdict — `RoundResult` records only the final attempt's source. The intermediate rejections appear in the live console output but not in the structured log.
- LLM-written `Disjoint` proofs are reliability-limited. In practice the LLM may hallucinate constructors that aren't in our `Val` type, or use tactics that don't terminate in the way it expects. The kernel correctly rejects all such attempts; the impact is that some genuinely-disjoint proposals may be rejected because the LLM couldn't write the proof, not because the property doesn't hold. (When the property *doesn't* hold — round 3 in current mode — proof failure is the correct outcome, not a limitation.)

## Open

### The Gödelian limit (not yet formalized)
The real incompleteness result would be: no program in the tower can verify `SafeEvolution` for itself. This requires a notion of "what programs can verify" that the current formalization doesn't have. Level N can verify modifications to level N-1, but not to itself — this parallels iterated reflection principles in logic, but making it a theorem needs more machinery.

### Richer modifications
Currently restricted to the guard+handler pattern. Black allows arbitrary code at the meta-level.

### Meta-continuations
A coinductive formalization (mirroring Black's lazy meta-continuation streams) would be more faithful than fuel.

### Fixpoint semantics
Define the tower semantics as a fixpoint of the "interpret the level below" operation (following Wand-Friedman). Connects to domain theory.

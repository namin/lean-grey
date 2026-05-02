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

A small loop in which Claude (via AWS Bedrock) proposes a `GuardedMod` in Lean source, and the Lean compiler plus the tower's policy decide whether to admit it. Three pieces:

- **`LeanBlack/Bedrock.lean`** — `invoke : Config → String → IO (Except String String)`, wrapping `aws bedrock-runtime invoke-model`. Reads AWS credentials from the standard chain (env vars or `~/.aws/credentials`), defaults to `us-east-1` and `us.anthropic.claude-sonnet-4-6`.
- **`LeanBlack/Elab.lean`** — `checkProposal` writes a wrapper file (imports `LeanBlack.Tower`, splices each previously-admitted mod as `def admitted_i : GuardedMod`, defines `proposal : GuardedMod where <LLM source>` and `witness : Val × List Val := <LLM source>`, then in `main` runs the policy gate; on admit it folds `priors` and `proposal` into a chained rule via `applyMod` and evaluates the witness against it). Spawns `lake env lean --run`. Outcome: `elabError | rejected | admitted (Option String)`, where the `Option String` is the `repr` of the witness's evaluated value. No in-process MetaM — the Lean compiler is the elaborator.
- **`LeanBlack/Runner.lean`** — composes them. The prompt asks the LLM for two ALL-CAPS sections: `PROPOSAL:` (the `where`-block fields) and `WITNESS:` (a `Val × List Val` term that exercises the proposal). The runner parses both sections, fixes the common first-line indent trim on the proposal, and loops. On `elabError`, it re-prompts with the prior attempt and Lean's diagnostic, retrying up to `Config.maxRetries` (default 1) before giving up on the round.

### Running

Prerequisites: `aws` CLI on PATH with Bedrock-enabled credentials, and the project built (`lake build`).

```bash
lake exe bedrock-smoke      # one-shot round trip ("READY")
lake exe proposal-smoke     # exercise admitted / rejected / elab-error
                            # on three hardcoded proposals
lake exe runner [N]         # N rounds of LLM-proposes / Lean-checks
                            # (default 3)
```

A typical 3-round run admits three mods, each with a witness that the wrapper evaluates against the chained rule. Sample output:

```
ROUND 1: bool combinator → witness (.bool true, [.num 7])  →  Val.num 7
ROUND 2: num subtract    → witness (.num 7, [.num 3])      →  Val.num 4
ROUND 3: num n*m+n       → witness (.num 6, [.num 3])      →  Val.num 24
```

Each value is the `repr` of `applyMod proposal (priors.foldl applyMod stdRule) v args`, computed inside the `lake env lean --run` subprocess.

### Scope and limits

The runner gates each proposal against `witnessPolicy stdWitnesses` over `stdRule` — the conservative-extension-of-base property. Each admitted modification is individually disjoint from stdRule's success cases (`+`, `-`, `*`, closures), so the composition of all admitted mods preserves stdRule's outputs everywhere stdRule succeeds. This is the safety property `install_safe` and `eval_tower_conservative` already prove; the runner is its LLM-driven counterpart.

The witness eval shows causal effect of the chained rule: each round's admit produces a value computed against `applyMod proposal (priors.foldl applyMod stdRule)`, so accumulated mods are part of the rule the witness runs against. (Whether a particular witness exercises *prior* mods or only the new one depends on which guards fire first under `applyMod`'s outer-wins semantics — for typical LLM-chosen witnesses, the just-added mod fires.)

Remaining caveats:

- The gate stays the rule-independent `witnessPolicy stdWitnesses`, so accepted-mod conflicts don't reject — round 3 can claim `.num` even if round 2 already did. This is the conservative-extension-of-base story, accepted as the design.
- Retry attempts overwrite the verdict — `RoundResult` records only the final attempt's source. If you want to inspect the full retry trace, `runOneRound` would need to accumulate intermediates.

## Open

### The Gödelian limit (not yet formalized)
The real incompleteness result would be: no program in the tower can verify `SafeEvolution` for itself. This requires a notion of "what programs can verify" that the current formalization doesn't have. Level N can verify modifications to level N-1, but not to itself — this parallels iterated reflection principles in logic, but making it a theorem needs more machinery.

### Richer modifications
Currently restricted to the guard+handler pattern. Black allows arbitrary code at the meta-level.

### Meta-continuations
A coinductive formalization (mirroring Black's lazy meta-continuation streams) would be more faithful than fuel.

### Fixpoint semantics
Define the tower semantics as a fixpoint of the "interpret the level below" operation (following Wand-Friedman). Connects to domain theory.

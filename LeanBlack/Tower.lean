/-
  A reflective tower with EM (exec-at-metalevel) and verified modifications.

  The evaluator can change its own apply rule during evaluation via EM.
  This is the reflective move: a program modifying its own evaluator.

  EM is governed: a policy gates which modifications are installed.
  Main theorem: with sound governance, EM can only produce conservative
  extensions of the original rule. Self-modification is safe.
-/

mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | closure : List String → Expr → List (String × Val) → Val
  | prim    : String → Val
  deriving Repr

inductive Expr where
  | num  : Int → Expr
  | bool : Bool → Expr
  | var  : String → Expr
  | ifte : Expr → Expr → Expr → Expr
  | lam  : List String → Expr → Expr
  | app  : List Expr → Expr
  | em   : Nat → Expr   -- exec-at-metalevel: install modification #n
  deriving Repr
end

abbrev Env := List (String × Val)
abbrev ApplyRule := Val → List Val → Option Val

structure GuardedMod where
  guard   : Val → Bool
  handler : Val → List Val → Option Val

def applyMod (m : GuardedMod) (r : ApplyRule) : ApplyRule :=
  fun v args => if m.guard v then m.handler v args else r v args

abbrev ModTable := List GuardedMod
abbrev Policy := GuardedMod → ApplyRule → Bool

def ConservativeExt (r₁ r₂ : ApplyRule) : Prop :=
  ∀ v args result, r₁ v args = some result → r₂ v args = some result

def Policy.Sound (p : Policy) (r : ApplyRule) : Prop :=
  ∀ m, p m r = true → ConservativeExt r (applyMod m r)

def Policy.UnivSound (p : Policy) : Prop := ∀ r, p.Sound r

def Env.lookup : Env → String → Option Val
  | [], _ => none
  | (k, v) :: rest, name => if k == name then some v else Env.lookup rest name

def Env.extend (env : Env) (params : List String) (args : List Val) : Env :=
  params.zip args ++ env

def applyPrim : String → List Val → Option Val
  | "+", [.num a, .num b] => some (.num (a + b))
  | "*", [.num a, .num b] => some (.num (a * b))
  | "-", [.num a, .num b] => some (.num (a - b))
  | _, _ => none

-- Result of evaluation: value + possibly updated rule
abbrev EvalResult := Option (Val × ApplyRule)
abbrev EvalListResult := Option (List Val × ApplyRule)

mutual
def eval (mods : ModTable) (policy : Policy) (fuel : Nat)
    (exp : Expr) (env : Env) (rule : ApplyRule) : EvalResult :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i => some (.num i, rule)
    | .bool b => some (.bool b, rule)
    | .var x =>
      match env.lookup x with
      | some v => some (v, rule)
      | none => none
    | .ifte c t e =>
      match eval mods policy n c env rule with
      | some (.bool false, rule') => eval mods policy n e env rule'
      | some (_, rule') => eval mods policy n t env rule'
      | none => none
    | .lam params body => some (.closure params body env, rule)
    | .app exprs =>
      match exprs with
      | [] => none
      | f :: args =>
        match eval mods policy n f env rule with
        | some (fv, rule') =>
          match evalList mods policy n args env rule' with
          | some (avs, rule'') =>
            match fv with
            | .closure params body cenv =>
              eval mods policy n body (Env.extend cenv params avs) rule''
            | _ =>
              match rule'' fv avs with
              | some v => some (v, rule'')
              | none => none
          | none => none
        | none => none
    | .em idx =>
      match mods[idx]? with
      | some mod =>
        if policy mod rule then
          some (.bool true, applyMod mod rule)
        else
          some (.bool false, rule)
      | none => some (.bool false, rule)

def evalList (mods : ModTable) (policy : Policy) (fuel : Nat)
    (exps : List Expr) (env : Env) (rule : ApplyRule) : EvalListResult :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exps with
    | [] => some ([], rule)
    | e :: rest =>
      match eval mods policy n e env rule with
      | some (v, rule') =>
        match evalList mods policy n rest env rule' with
        | some (vs, rule'') => some (v :: vs, rule'')
        | none => none
      | none => none
end

-- Helpers and instances
def stdRule : ApplyRule
  | .prim name, args => applyPrim name args
  | _, _ => none

def initEnv : Env :=
  [("+", .prim "+"), ("-", .prim "-"), ("*", .prim "*")]

def acceptAll : Policy := fun _ _ => true
def rejectAll : Policy := fun _ _ => false

def multnMod : GuardedMod where
  guard v := match v with | .num _ => true | _ => false
  handler v args := match v with
    | .num n =>
      let nums := args.filterMap (fun v => match v with | .num i => some i | _ => none)
      if nums.length == args.length
      then some (.num (nums.foldl (· * ·) n))
      else none
    | _ => none

-- Extract just the value for testing (ApplyRule has no Repr)
def evalVal (mods : ModTable) (policy : Policy) (fuel : Nat)
    (exp : Expr) (env : Env) (rule : ApplyRule) : Option Val :=
  (eval mods policy fuel exp env rule).map Prod.fst

-- Smoke tests
#eval evalVal [] acceptAll 100 (.app [.var "+", .num 1, .num 2]) initEnv stdRule
#eval evalVal [] acceptAll 100 (.app [.num 2, .num 3, .num 4]) initEnv stdRule

-- Helper to test EM: evaluate em, then evaluate expr with the resulting rule
def evalAfterEM (mods : ModTable) (policy : Policy) (fuel : Nat)
    (emIdx : Nat) (exp : Expr) (env : Env) (rule : ApplyRule) : Option Val :=
  match eval mods policy fuel (.em emIdx) env rule with
  | some (_, rule') => evalVal mods policy fuel exp env rule'
  | none => none

#eval evalAfterEM [multnMod] acceptAll 100 0
  (.app [.num 2, .num 3, .num 4]) initEnv stdRule  -- 24

#eval evalAfterEM [multnMod] rejectAll 100 0
  (.app [.num 2, .num 3, .num 4]) initEnv stdRule  -- none (rejected)

#eval evalAfterEM [multnMod] acceptAll 100 0
  (.app [.var "+", .num 1, .num 2]) initEnv stdRule  -- 3 (preserved)

/-
  Basic lemmas
-/

theorem conservative_refl (r : ApplyRule) : ConservativeExt r r :=
  fun _ _ _ h => h

theorem conservative_trans {r₁ r₂ r₃ : ApplyRule} :
    ConservativeExt r₁ r₂ → ConservativeExt r₂ r₃ → ConservativeExt r₁ r₃ :=
  fun h₁₂ h₂₃ v args res h => h₂₃ v args res (h₁₂ v args res h)

def Disjoint (m : GuardedMod) (r : ApplyRule) : Prop :=
  ∀ v args, m.guard v = true → r v args = none

theorem disjoint_conservative (m : GuardedMod) (r : ApplyRule) :
    Disjoint m r → ConservativeExt r (applyMod m r) := by
  intro hdis v args result h
  simp only [applyMod]
  split
  · next hg => exact absurd h (by simp [hdis v args hg])
  · exact h

/-
  THE MAIN THEOREM: governed EM preserves conservative extension.

  If governance is universally sound, then evaluating ANY program
  (which may use EM to modify the evaluator) yields a rule that
  is a conservative extension of the original.

  eval_rule_conservative: self-modification under governance is safe.
-/

mutual
theorem eval_rule_conservative (mods : ModTable) (policy : Policy)
    (h_sound : policy.UnivSound)
    (fuel : Nat) (exp : Expr) (env : Env) (rule rule' : ApplyRule) (v : Val) :
    eval mods policy fuel exp env rule = some (v, rule') →
    ConservativeExt rule rule' := by
  match fuel with
  | 0 => simp [eval]
  | n + 1 =>
    match exp with
    | .num _ | .bool _ | .lam _ _ =>
      simp only [eval]; intro h; obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact conservative_refl _
    | .var x =>
      simp only [eval]; intro h
      split at h <;> simp at h
      obtain ⟨-, rfl⟩ := h
      exact conservative_refl _
    | .em idx =>
      simp only [eval]; intro h
      split at h
      · next mod _ =>
        split at h
        · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact h_sound rule mod (by assumption)
        · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact conservative_refl _
      · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact conservative_refl _
    | .ifte c t e =>
      simp only [eval]; intro h
      match hc : eval mods policy n c env rule with
      | none => simp [hc] at h
      | some (cv, rc) =>
        have hrc := eval_rule_conservative mods policy h_sound n c env rule rc cv hc
        simp [hc] at h
        match cv with
        | .bool false =>
          simp at h
          exact conservative_trans hrc
            (eval_rule_conservative mods policy h_sound n e env rc rule' v h)
        | .bool true =>
          simp at h
          exact conservative_trans hrc
            (eval_rule_conservative mods policy h_sound n t env rc rule' v h)
        | .num _ | .closure _ _ _ | .prim _ =>
          simp at h
          exact conservative_trans hrc
            (eval_rule_conservative mods policy h_sound n t env rc rule' v h)
    | .app exprs =>
      simp only [eval]; intro h
      match exprs with
      | [] => simp at h
      | f :: args =>
        simp only [eval] at h
        match hf : eval mods policy n f env rule with
        | none => simp [hf] at h
        | some (fv, rf) =>
          simp [hf] at h
          have hrf := eval_rule_conservative mods policy h_sound n f env rule rf fv hf
          match ha : evalList mods policy n args env rf with
          | none => simp [ha] at h
          | some (avs, ra) =>
            simp [ha] at h
            have hra := evalList_rule_conservative mods policy h_sound n args env rf ra avs ha
            have h_fa := conservative_trans hrf hra
            match fv with
            | .closure params body cenv =>
              exact conservative_trans h_fa
                (eval_rule_conservative mods policy h_sound n body
                  (Env.extend cenv params avs) ra rule' v h)
            | .num _ | .bool _ | .prim _ =>
              simp at h
              split at h <;> simp at h
              obtain ⟨-, rfl⟩ := h
              exact h_fa
termination_by fuel

theorem evalList_rule_conservative (mods : ModTable) (policy : Policy)
    (h_sound : policy.UnivSound)
    (fuel : Nat) (exps : List Expr) (env : Env) (rule rule' : ApplyRule) (vs : List Val) :
    evalList mods policy fuel exps env rule = some (vs, rule') →
    ConservativeExt rule rule' := by
  match fuel with
  | 0 => simp [evalList]
  | n + 1 =>
    match exps with
    | [] =>
      simp only [evalList]; intro h
      obtain ⟨-, rfl⟩ := h
      exact conservative_refl _
    | e :: rest =>
      simp only [evalList]; intro h
      match he : eval mods policy n e env rule with
      | none => simp [he] at h
      | some (val, re) =>
        simp [he] at h
        have hre := eval_rule_conservative mods policy h_sound n e env rule re val he
        match hr : evalList mods policy n rest env re with
        | none => simp [hr] at h
        | some (vs', rr) =>
          simp [hr] at h
          obtain ⟨-, rfl⟩ := h
          exact conservative_trans hre
            (evalList_rule_conservative mods policy h_sound n rest env re rr vs' hr)
termination_by fuel
end

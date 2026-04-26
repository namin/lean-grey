/-
  A reflective tower with verified modifications.

  The key idea: the evaluator is parameterized by its apply rule.
  This mirrors Black, where base-apply is a binding in the meta-environment
  that can be swapped out. A "reflective modification" is a new apply rule.
  Conservative extension means: old defined behavior is preserved.

  The tower theorem: if the apply rule is conservatively extended,
  then the evaluator (for all programs) is conservatively extended.
  Component-level conservation lifts to program-level conservation.
-/

-- Minimal expression type
inductive Expr where
  | num  : Int → Expr
  | bool : Bool → Expr
  | var  : String → Expr
  | ifte : Expr → Expr → Expr → Expr
  | lam  : List String → Expr → Expr
  | app  : List Expr → Expr
  deriving Repr, BEq, Inhabited

-- Minimal value type
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | closure : List String → Expr → List (String × Val) → Val
  | prim    : String → Val
  deriving Repr, BEq, Inhabited

abbrev Env := List (String × Val)

def Env.lookup : Env → String → Option Val
  | [], _ => none
  | (k, v) :: rest, name => if k == name then some v else Env.lookup rest name

def Env.extend (env : Env) (params : List String) (args : List Val) : Env :=
  params.zip args ++ env

-- An ApplyRule handles non-closure application.
-- Closures (lambda) are always handled uniformly by eval.
-- This is the replaceable component — Black's base-apply dispatch.
abbrev ApplyRule := Val → List Val → Option Val

-- The evaluator, parameterized by its apply rule.
-- This is the core of the tower: eval is a FUNCTOR from apply rules
-- to program evaluators.
mutual
def eval (rule : ApplyRule) (fuel : Nat) (exp : Expr) (env : Env) : Option Val :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i => some (.num i)
    | .bool b => some (.bool b)
    | .var x => env.lookup x
    | .ifte c t e =>
      match eval rule n c env with
      | some (.bool false) => eval rule n e env
      | some _ => eval rule n t env
      | none => none
    | .lam params body => some (.closure params body env)
    | .app exprs =>
      match exprs with
      | [] => none
      | f :: args =>
        match eval rule n f env with
        | some fv =>
          match evalList rule n args env with
          | some avs =>
            match fv with
            | .closure params body cenv =>
              eval rule n body (Env.extend cenv params avs)
            | _ => rule fv avs
          | none => none
        | none => none

def evalList (rule : ApplyRule) (fuel : Nat) (exps : List Expr) (env : Env)
    : Option (List Val) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exps with
    | [] => some []
    | e :: rest =>
      match eval rule n e env with
      | some v =>
        match evalList rule n rest env with
        | some vs => some (v :: vs)
        | none => none
      | none => none
end

-- Standard primitives
def applyPrim : String → List Val → Option Val
  | "+", [.num a, .num b] => some (.num (a + b))
  | "*", [.num a, .num b] => some (.num (a * b))
  | "-", [.num a, .num b] => some (.num (a - b))
  | _, _ => none

-- The standard apply rule: only handles primitives
def stdRule : ApplyRule
  | .prim name, args => applyPrim name args
  | _, _ => none

-- The multn apply rule: numbers multiply their operands
def multnRule : ApplyRule
  | .num n, args =>
    match args.filterMap (fun v => match v with | .num i => some i | _ => none) with
    | nums => if nums.length == args.length
              then some (.num (nums.foldl (· * ·) n))
              else none
  | .prim name, args => applyPrim name args
  | _, _ => none

-- Standard environment
def initEnv : Env :=
  [("+", .prim "+"), ("-", .prim "-"), ("*", .prim "*")]

-- Smoke tests
#eval eval stdRule 100 (.app [.var "+", .num 1, .num 2]) initEnv
#eval eval stdRule 100 (.app [.num 2, .num 3, .num 4]) initEnv  -- none
#eval eval multnRule 100 (.app [.num 2, .num 3, .num 4]) initEnv  -- 24
#eval eval multnRule 100 (.app [.var "+", .num 1, .num 2]) initEnv  -- 3

/-
  Conservative extension: the core relation.
-/

def ConservativeExt (r₁ r₂ : ApplyRule) : Prop :=
  ∀ v args result, r₁ v args = some result → r₂ v args = some result

theorem conservative_refl (r : ApplyRule) : ConservativeExt r r :=
  fun _ _ _ h => h

theorem conservative_trans {r₁ r₂ r₃ : ApplyRule} :
    ConservativeExt r₁ r₂ → ConservativeExt r₂ r₃ → ConservativeExt r₁ r₃ :=
  fun h₁₂ h₂₃ v args res h => h₂₃ v args res (h₁₂ v args res h)

/-
  Guarded modifications: the multn pattern.
  A guard + handler, falling through to the original rule.
-/

structure GuardedMod where
  guard   : Val → Bool
  handler : Val → List Val → Option Val

def applyMod (m : GuardedMod) (r : ApplyRule) : ApplyRule :=
  fun v args => if m.guard v then m.handler v args else r v args

def Disjoint (m : GuardedMod) (r : ApplyRule) : Prop :=
  ∀ v args, m.guard v = true → r v args = none

-- THE CORE THEOREM: disjoint guard implies conservative extension.
theorem disjoint_conservative (m : GuardedMod) (r : ApplyRule) :
    Disjoint m r → ConservativeExt r (applyMod m r) := by
  intro hdis v args result h
  simp only [applyMod]
  split
  · next hg => exact absurd h (by simp [hdis v args hg, h])
  · exact h

/-
  THE LIFTING THEOREM: conservative extension at the apply-rule level
  implies conservative extension at the program level.

  This is the non-trivial theorem: it says the evaluator is monotone
  w.r.t. conservative extension. Modifying the component preserves
  the behavior of all programs.
-/

-- The proof is by mutual induction on fuel.
-- Each expression case is routine: recursive calls use the IH,
-- and the apply-rule call uses the conservative extension hypothesis.
mutual
theorem eval_monotone (r₁ r₂ : ApplyRule) (hc : ConservativeExt r₁ r₂)
    (fuel : Nat) (exp : Expr) (env : Env) (v : Val) :
    eval r₁ fuel exp env = some v → eval r₂ fuel exp env = some v := by
  match fuel with
  | 0 => simp [eval]
  | n + 1 =>
    match exp with
    | .num _ | .bool _ | .var _ | .lam _ _ =>
      simp only [eval]; exact id
    | .ifte c t e =>
      simp only [eval]
      intro h
      match hce : eval r₁ n c env with
      | none => simp [hce] at h
      | some (.bool false) =>
        simp [hce] at h
        have := eval_monotone r₁ r₂ hc n c env _ hce
        simp [this]
        exact eval_monotone r₁ r₂ hc n e env v h
      | some (.bool true) =>
        simp [hce] at h
        have := eval_monotone r₁ r₂ hc n c env _ hce
        simp [this]
        exact eval_monotone r₁ r₂ hc n t env v h
      | some (.num _) =>
        simp [hce] at h
        have := eval_monotone r₁ r₂ hc n c env _ hce
        simp [this]
        exact eval_monotone r₁ r₂ hc n t env v h
      | some (.closure _ _ _) =>
        simp [hce] at h
        have := eval_monotone r₁ r₂ hc n c env _ hce
        simp [this]
        exact eval_monotone r₁ r₂ hc n t env v h
      | some (.prim _) =>
        simp [hce] at h
        have := eval_monotone r₁ r₂ hc n c env _ hce
        simp [this]
        exact eval_monotone r₁ r₂ hc n t env v h
    | .app exprs =>
      simp only [eval]
      intro h
      match exprs with
      | [] => simp [eval] at h
      | f :: args =>
        simp only [eval] at h ⊢
        match hf : eval r₁ n f env with
        | none => simp [hf] at h
        | some fv =>
          simp [hf] at h
          have hf' := eval_monotone r₁ r₂ hc n f env fv hf
          simp [hf']
          match hal : evalList r₁ n args env with
          | none => simp [hal] at h
          | some avs =>
            simp [hal] at h
            have hal' := evalList_monotone r₁ r₂ hc n args env avs hal
            simp [hal']
            match fv with
            | .closure params body cenv =>
              exact eval_monotone r₁ r₂ hc n body (Env.extend cenv params avs) v h
            | .num _ =>
              simp at h; exact hc _ avs v h
            | .bool _ =>
              simp at h; exact hc _ avs v h
            | .prim _ =>
              simp at h; exact hc _ avs v h
termination_by fuel

theorem evalList_monotone (r₁ r₂ : ApplyRule) (hc : ConservativeExt r₁ r₂)
    (fuel : Nat) (exps : List Expr) (env : Env) (vs : List Val) :
    evalList r₁ fuel exps env = some vs → evalList r₂ fuel exps env = some vs := by
  match fuel with
  | 0 => simp [evalList]
  | n + 1 =>
    match exps with
    | [] => simp only [evalList]; exact id
    | e :: rest =>
      simp only [evalList]
      intro h
      match he : eval r₁ n e env with
      | none => simp [he] at h
      | some val =>
        simp [he] at h
        have he' := eval_monotone r₁ r₂ hc n e env val he
        simp [he']
        match hr : evalList r₁ n rest env with
        | none => simp [hr] at h
        | some vs' =>
          simp [hr] at h
          have hr' := evalList_monotone r₁ r₂ hc n rest env vs' hr
          simp [hr']
          exact h
termination_by fuel
end
/-
  TOWER: a sequence of apply rules, one per level.
  Level n+1 governs modifications to level n.
-/

abbrev Tower := Nat → ApplyRule

-- Modify level n of the tower
def Tower.modify (t : Tower) (n : Nat) (m : GuardedMod) : Tower :=
  fun k => if k == n then applyMod m (t k) else t k

-- A governance policy: decides whether a modification is allowed
abbrev Policy := GuardedMod → ApplyRule → Bool

-- A policy is sound if every modification it accepts is conservative
def Policy.Sound (p : Policy) (r : ApplyRule) : Prop :=
  ∀ m, p m r = true → ConservativeExt r (applyMod m r)

-- Tower with governance: each level has a rule and a policy for the level below
structure GovernedTower where
  rule   : Nat → ApplyRule
  policy : Nat → Policy
  sound  : ∀ n, (policy n).Sound (rule n)

-- If governance is sound and a modification passes, tower semantics is preserved.
-- This combines disjoint_conservative (or whatever the policy guarantees)
-- with eval_monotone (the lifting theorem).
theorem governed_modification_safe (gt : GovernedTower) (n : Nat) (m : GuardedMod)
    (h_pass : gt.policy n m (gt.rule n) = true)
    (fuel : Nat) (exp : Expr) (env : Env) (v : Val) :
    eval (gt.rule n) fuel exp env = some v →
    eval (applyMod m (gt.rule n)) fuel exp env = some v := by
  intro h_eval
  have h_cons := gt.sound n m h_pass
  exact eval_monotone _ _ h_cons fuel exp env v h_eval

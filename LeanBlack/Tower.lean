/-
  A reflective tower with EM, level-shifting, and verified modifications.

  The tower has multiple levels. EM shifts evaluation up one level.
  `install` at level N modifies tower(N) — the apply rule that level N-1
  uses for application dispatch. This mirrors Black: EM gives access to the
  meta-level, where the evaluator's components are modifiable bindings.

  Nested EM: (em (em (install 0))) at level 0 shifts to level 2 and
  modifies tower(2), which is the rule used at level 1. This is
  meta-meta-modification: changing how the meta-level works.

  Main theorem: with sound governance at every level, evaluating any
  program (with EM and install at any depth) produces a tower where
  every level's rule is a conservative extension of the original.
-/

mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | closure : List String → Expr → List (String × Val) → Val
  | prim    : String → Val
  deriving Repr

inductive Expr where
  | num     : Int → Expr
  | bool    : Bool → Expr
  | var     : String → Expr
  | ifte    : Expr → Expr → Expr → Expr
  | lam     : List String → Expr → Expr
  | app     : List Expr → Expr
  | em      : Expr → Expr    -- shift up one level and evaluate body
  | install : Nat → Expr     -- install modification #n at this level
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

-- Tower state: each level n has an apply rule tower(n).
-- Level k uses tower(k+1) for apply dispatch.
-- install at level k modifies tower(k).
-- So (em (install 0)) at level k modifies tower(k+1), the rule for level k.
abbrev TowerState := Nat → ApplyRule

def TowerState.update (t : TowerState) (n : Nat) (r : ApplyRule) : TowerState :=
  fun k => if k == n then r else t k

def ConservativeExt (r₁ r₂ : ApplyRule) : Prop :=
  ∀ v args result, r₁ v args = some result → r₂ v args = some result

-- Governance: policy at each level
-- policy(n) governs modifications to tower(n)
abbrev Governance := Nat → Policy

def Governance.AllSound (g : Governance) (t : TowerState) : Prop :=
  ∀ n m, g n m (t n) = true → ConservativeExt (t n) (applyMod m (t n))

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

-- Result types
abbrev EvalResult := Option (Val × TowerState)

/-
  The evaluator with tower structure.

  eval operates at a given `level`.
  - Apply dispatch uses tower(level + 1): the rule managed by the level above.
  - (em body) evaluates body at level + 1.
  - (install n) modifies tower(level) — the rule used by level - 1.
    Governed by governance(level).

  Fuel bounds ALL computation (across levels).
-/
mutual
def eval (mods : ModTable) (gov : Governance) (fuel : Nat)
    (level : Nat) (exp : Expr) (env : Env) (tower : TowerState)
    : EvalResult :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exp with
    | .num i => some (.num i, tower)
    | .bool b => some (.bool b, tower)
    | .var x =>
      match env.lookup x with
      | some v => some (v, tower)
      | none => none
    | .ifte c t e =>
      match eval mods gov n level c env tower with
      | some (.bool false, tower') => eval mods gov n level e env tower'
      | some (_, tower') => eval mods gov n level t env tower'
      | none => none
    | .lam params body => some (.closure params body env, tower)
    | .app exprs =>
      match exprs with
      | [] => none
      | f :: args =>
        match eval mods gov n level f env tower with
        | some (fv, tower') =>
          match evalList mods gov n level args env tower' with
          | some (avs, tower'') =>
            match fv with
            | .closure params body cenv =>
              eval mods gov n level body (Env.extend cenv params avs) tower''
            | _ =>
              -- Apply dispatch: use rule from level ABOVE
              match (tower'' (level + 1)) fv avs with
              | some v => some (v, tower'')
              | none => none
          | none => none
        | none => none
    -- EM: shift up one level
    | .em body =>
      eval mods gov n (level + 1) body env tower
    -- INSTALL: modify this level's rule (used by level below)
    | .install modIdx =>
      match mods[modIdx]? with
      | some mod =>
        let rule := tower level
        if gov level mod rule then
          some (.bool true, tower.update level (applyMod mod rule))
        else
          some (.bool false, tower)
      | none => some (.bool false, tower)

def evalList (mods : ModTable) (gov : Governance) (fuel : Nat)
    (level : Nat) (exps : List Expr) (env : Env) (tower : TowerState)
    : Option (List Val × TowerState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exps with
    | [] => some ([], tower)
    | e :: rest =>
      match eval mods gov n level e env tower with
      | some (v, tower') =>
        match evalList mods gov n level rest env tower' with
        | some (vs, tower'') => some (v :: vs, tower'')
        | none => none
      | none => none
end

-- Standard setup
def stdRule : ApplyRule
  | .prim name, args => applyPrim name args
  | _, _ => none

def initTower : TowerState := fun _ => stdRule

def initEnv : Env :=
  [("+", .prim "+"), ("-", .prim "-"), ("*", .prim "*")]

def acceptAll : Governance := fun _ _ _ => true
def rejectAll : Governance := fun _ _ _ => false

def multnMod : GuardedMod where
  guard v := match v with | .num _ => true | _ => false
  handler v args := match v with
    | .num n =>
      let nums := args.filterMap (fun v => match v with | .num i => some i | _ => none)
      if nums.length == args.length
      then some (.num (nums.foldl (· * ·) n))
      else none
    | _ => none

-- Helper: extract just the value
def evalVal (mods : ModTable) (gov : Governance) (fuel : Nat) (level : Nat)
    (exp : Expr) (env : Env) (tower : TowerState) : Option Val :=
  (eval mods gov fuel level exp env tower).map Prod.fst

-- Smoke tests

-- Basic arithmetic at level 0
#eval evalVal [] acceptAll 100 0 (.app [.var "+", .num 1, .num 2]) initEnv initTower
-- => some 3

-- (2 3 4) fails without multn
#eval evalVal [] acceptAll 100 0 (.app [.num 2, .num 3, .num 4]) initEnv initTower
-- => none

-- (em (install 0)): at level 0, shift to level 1, install multn into tower(1)
-- tower(1) is the rule used by level 0
-- Then (2 3 4) at level 0 should work
-- We need a "begin" or sequencing. Let's use ifte as sequencing:
-- (if (em (install 0)) (2 3 4) (2 3 4))
#eval evalVal [multnMod] acceptAll 100 0
  (.ifte (.em (.install 0)) (.app [.num 2, .num 3, .num 4]) (.num 0))
  initEnv initTower
-- => some 24

-- Same but with rejectAll: install fails, (2 3 4) still fails
#eval evalVal [multnMod] rejectAll 100 0
  (.ifte (.em (.install 0)) (.app [.num 2, .num 3, .num 4]) (.num 0))
  initEnv initTower
-- => none

-- (+ 1 2) still works after EM install (conservative extension)
#eval evalVal [multnMod] acceptAll 100 0
  (.ifte (.em (.install 0)) (.app [.var "+", .num 1, .num 2]) (.num 0))
  initEnv initTower
-- => some 3

-- NESTED EM: (em (em (install 0))) at level 0
-- shifts to level 2, installs into tower(2), which is the rule for level 1
#eval evalVal [multnMod] acceptAll 100 0
  (.em (.em (.install 0)))
  initEnv initTower
-- => some true (installed at level 2)

/-
  Basic lemmas
-/

theorem conservative_refl (r : ApplyRule) : ConservativeExt r r :=
  fun _ _ _ h => h

theorem conservative_trans {r₁ r₂ r₃ : ApplyRule} :
    ConservativeExt r₁ r₂ → ConservativeExt r₂ r₃ → ConservativeExt r₁ r₃ :=
  fun h₁₂ h₂₃ v args res h => h₂₃ v args res (h₁₂ v args res h)

-- TowerState.update only changes one level
theorem update_other (t : TowerState) (n k : Nat) (r : ApplyRule) :
    k ≠ n → (t.update n r) k = t k := by
  intro hne; simp [TowerState.update, hne]

theorem update_same (t : TowerState) (n : Nat) (r : ApplyRule) :
    (t.update n r) n = r := by
  simp [TowerState.update]

-- Pointwise conservative extension for tower states
def TowerConservative (t₁ t₂ : TowerState) : Prop :=
  ∀ n, ConservativeExt (t₁ n) (t₂ n)

theorem tower_conservative_refl (t : TowerState) : TowerConservative t t :=
  fun n => conservative_refl (t n)

theorem tower_conservative_trans {t₁ t₂ t₃ : TowerState} :
    TowerConservative t₁ t₂ → TowerConservative t₂ t₃ → TowerConservative t₁ t₃ :=
  fun h₁₂ h₂₃ n => conservative_trans (h₁₂ n) (h₂₃ n)

-- Updating with a conservative extension preserves tower conservativeness
theorem update_conservative (t : TowerState) (n : Nat) (r : ApplyRule)
    (h : ConservativeExt (t n) r) :
    TowerConservative t (t.update n r) := by
  intro k
  by_cases hk : k = n
  · subst hk; rw [update_same]; exact h
  · rw [update_other _ _ _ _ hk]; exact conservative_refl _

/-
  THE MAIN THEOREM: tower safety under governed self-modification.

  If governance is sound at every level for the current tower state,
  then evaluating any program (with EM and install at any depth)
  produces a tower where every level's rule is a conservative extension
  of the original.
-/

-- Governance is "persistently sound": sound for any conservative extension
-- of the original tower. Needed because the tower changes during evaluation.
def Governance.PersistentlySound (g : Governance) (t₀ : TowerState) : Prop :=
  ∀ t, TowerConservative t₀ t → ∀ n m, g n m (t n) = true →
    ConservativeExt (t n) (applyMod m (t n))

mutual
theorem eval_tower_conservative (mods : ModTable) (gov : Governance)
    (t₀ : TowerState) (h_sound : gov.PersistentlySound t₀)
    (fuel : Nat) (level : Nat) (exp : Expr) (env : Env)
    (tower : TowerState) (h_tc : TowerConservative t₀ tower)
    (v : Val) (tower' : TowerState) :
    eval mods gov fuel level exp env tower = some (v, tower') →
    TowerConservative tower tower' := by
  match fuel with
  | 0 => simp [eval]
  | n + 1 =>
    match exp with
    | .num _ | .bool _ | .lam _ _ =>
      simp only [eval]; intro h; obtain ⟨-, rfl⟩ := h
      exact tower_conservative_refl _
    | .var x =>
      simp only [eval]; intro h
      split at h <;> simp at h
      obtain ⟨-, rfl⟩ := h
      exact tower_conservative_refl _
    | .ifte c t e =>
      simp only [eval]; intro h
      match hc : eval mods gov n level c env tower with
      | none => simp [hc] at h
      | some (cv, tc) =>
        simp [hc] at h
        have htc := eval_tower_conservative mods gov t₀ h_sound n level c env
          tower h_tc cv tc hc
        have h_tc' := tower_conservative_trans h_tc htc
        match cv with
        | .bool false =>
          simp at h
          exact tower_conservative_trans htc
            (eval_tower_conservative mods gov t₀ h_sound n level e env tc h_tc' v tower' h)
        | .bool true | .num _ | .closure _ _ _ | .prim _ =>
          simp at h
          exact tower_conservative_trans htc
            (eval_tower_conservative mods gov t₀ h_sound n level t env tc h_tc' v tower' h)
    | .app exprs =>
      simp only [eval]; intro h
      match exprs with
      | [] => simp at h
      | f :: args =>
        simp only [eval] at h
        match hf : eval mods gov n level f env tower with
        | none => simp [hf] at h
        | some (fv, tf) =>
          simp [hf] at h
          have htf := eval_tower_conservative mods gov t₀ h_sound n level f env
            tower h_tc fv tf hf
          have h_tc_f := tower_conservative_trans h_tc htf
          match ha : evalList mods gov n level args env tf with
          | none => simp [ha] at h
          | some (avs, ta) =>
            simp [ha] at h
            have hta := evalList_tower_conservative mods gov t₀ h_sound n level args env
              tf h_tc_f avs ta ha
            have h_fa := tower_conservative_trans htf hta
            have h_tc_a := tower_conservative_trans h_tc_f hta
            match fv with
            | .closure params body cenv =>
              exact tower_conservative_trans h_fa
                (eval_tower_conservative mods gov t₀ h_sound n level body
                  (Env.extend cenv params avs) ta h_tc_a v tower' h)
            | .num _ | .bool _ | .prim _ =>
              simp at h; split at h <;> simp at h
              obtain ⟨-, rfl⟩ := h; exact h_fa
    -- EM: level-shift. Evaluate body at level + 1.
    | .em body =>
      simp only [eval]; intro h
      exact eval_tower_conservative mods gov t₀ h_sound n (level + 1) body env
        tower h_tc v tower' h
    -- INSTALL: modify tower(level), governed by gov(level).
    | .install modIdx =>
      simp only [eval]; intro h
      split at h
      · next mod _ =>
        split at h
        · next h_pass =>
          obtain ⟨-, rfl⟩ := h
          exact update_conservative tower level _ (h_sound tower h_tc level mod h_pass)
        · obtain ⟨-, rfl⟩ := h; exact tower_conservative_refl _
      · obtain ⟨-, rfl⟩ := h; exact tower_conservative_refl _
termination_by fuel

theorem evalList_tower_conservative (mods : ModTable) (gov : Governance)
    (t₀ : TowerState) (h_sound : gov.PersistentlySound t₀)
    (fuel : Nat) (level : Nat) (exps : List Expr) (env : Env)
    (tower : TowerState) (h_tc : TowerConservative t₀ tower)
    (vs : List Val) (tower' : TowerState) :
    evalList mods gov fuel level exps env tower = some (vs, tower') →
    TowerConservative tower tower' := by
  match fuel with
  | 0 => simp [evalList]
  | n + 1 =>
    match exps with
    | [] =>
      simp only [evalList]; intro h; obtain ⟨-, rfl⟩ := h
      exact tower_conservative_refl _
    | e :: rest =>
      simp only [evalList]; intro h
      match he : eval mods gov n level e env tower with
      | none => simp [he] at h
      | some (val, te) =>
        simp [he] at h
        have hte := eval_tower_conservative mods gov t₀ h_sound n level e env
          tower h_tc val te he
        have h_tc_e := tower_conservative_trans h_tc hte
        match hr : evalList mods gov n level rest env te with
        | none => simp [hr] at h
        | some (vs', tr) =>
          simp [hr] at h; obtain ⟨-, rfl⟩ := h
          exact tower_conservative_trans hte
            (evalList_tower_conservative mods gov t₀ h_sound n level rest env
              te h_tc_e vs' tr hr)
termination_by fuel
end

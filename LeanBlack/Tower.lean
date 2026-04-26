/-
  A reflective tower with EM, level-shifting, and reflective governance.

  Each level has an apply rule AND a governance policy. Both are part of
  the tower state. Both are modifiable via EM:
  - (install n): modify this level's apply rule, governed by this level's policy
  - (installPolicy n): replace this level's policy

  The tower governs its own governance. Level N+2 can modify level N+1's
  policy, which changes what modifications level N+1 allows to level N.

  Main theorems:
  1. Tower safety: governed modifications preserve conservative extension.
  2. Governance coherence: if replacement policies are universally sound,
     then tower soundness is maintained across policy changes.
-/

mutual
inductive Val where
  | num     : Int → Val
  | bool    : Bool → Val
  | closure : List String → Expr → List (String × Val) → Val
  | prim    : String → Val
  deriving Repr

inductive Expr where
  | num           : Int → Expr
  | bool          : Bool → Expr
  | var           : String → Expr
  | ifte          : Expr → Expr → Expr → Expr
  | lam           : List String → Expr → Expr
  | app           : List Expr → Expr
  | em            : Expr → Expr    -- shift up one level
  | install       : Nat → Expr     -- install rule modification at this level
  | installPolicy : Nat → Expr     -- replace policy at this level
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
abbrev PolicyTable := List Policy

-- Each level has a rule and a policy
structure LevelState where
  rule : ApplyRule
  policy : Policy

-- Tower state: each level has a LevelState
abbrev TowerState := Nat → LevelState

def TowerState.update (t : TowerState) (n : Nat) (ls : LevelState) : TowerState :=
  fun k => if k == n then ls else t k

def ConservativeExt (r₁ r₂ : ApplyRule) : Prop :=
  ∀ v args result, r₁ v args = some result → r₂ v args = some result

-- A policy is sound w.r.t. a rule
def Policy.Sound (p : Policy) (r : ApplyRule) : Prop :=
  ∀ m, p m r = true → ConservativeExt r (applyMod m r)

-- A policy is universally sound (sound for ANY rule)
def Policy.UnivSound (p : Policy) : Prop :=
  ∀ r, p.Sound r

-- Tower soundness: every level's policy is sound for its rule
def TowerSound (t : TowerState) : Prop :=
  ∀ n, (t n).policy.Sound (t n).rule

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

/-
  The evaluator.

  - Apply dispatch at level L uses (tower (L+1)).rule
  - (em body) evaluates body at level + 1
  - (install n) modifies (tower level).rule, checked by (tower level).policy
  - (installPolicy n) replaces (tower level).policy from the policy table
-/
mutual
def eval (mods : ModTable) (ptable : PolicyTable) (fuel : Nat)
    (level : Nat) (exp : Expr) (env : Env) (tower : TowerState)
    : Option (Val × TowerState) :=
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
      match eval mods ptable n level c env tower with
      | some (.bool false, tower') => eval mods ptable n level e env tower'
      | some (_, tower') => eval mods ptable n level t env tower'
      | none => none
    | .lam params body => some (.closure params body env, tower)
    | .app exprs =>
      match exprs with
      | [] => none
      | f :: args =>
        match eval mods ptable n level f env tower with
        | some (fv, tower') =>
          match evalList mods ptable n level args env tower' with
          | some (avs, tower'') =>
            match fv with
            | .closure params body cenv =>
              eval mods ptable n level body (Env.extend cenv params avs) tower''
            | _ =>
              match (tower'' (level + 1)).rule fv avs with
              | some v => some (v, tower'')
              | none => none
          | none => none
        | none => none
    -- EM: shift up one level
    | .em body =>
      eval mods ptable n (level + 1) body env tower
    -- INSTALL: modify this level's rule, governed by this level's policy
    | .install modIdx =>
      let ls := tower level
      match mods[modIdx]? with
      | some mod =>
        if ls.policy mod ls.rule then
          some (.bool true, tower.update level { ls with rule := applyMod mod ls.rule })
        else
          some (.bool false, tower)
      | none => some (.bool false, tower)
    -- INSTALL POLICY: replace this level's policy
    | .installPolicy polIdx =>
      match ptable[polIdx]? with
      | some newPolicy =>
        let ls := tower level
        some (.bool true, tower.update level { ls with policy := newPolicy })
      | none => some (.bool false, tower)

def evalList (mods : ModTable) (ptable : PolicyTable) (fuel : Nat)
    (level : Nat) (exps : List Expr) (env : Env) (tower : TowerState)
    : Option (List Val × TowerState) :=
  match fuel with
  | 0 => none
  | n + 1 =>
    match exps with
    | [] => some ([], tower)
    | e :: rest =>
      match eval mods ptable n level e env tower with
      | some (v, tower') =>
        match evalList mods ptable n level rest env tower' with
        | some (vs, tower'') => some (v :: vs, tower'')
        | none => none
      | none => none
end

-- Standard setup
def stdRule : ApplyRule
  | .prim name, args => applyPrim name args
  | _, _ => none

def acceptAllPolicy : Policy := fun _ _ => true
def rejectAllPolicy : Policy := fun _ _ => false

def initTower : TowerState := fun _ => { rule := stdRule, policy := acceptAllPolicy }
def guardedTower : TowerState := fun _ => { rule := stdRule, policy := rejectAllPolicy }

def initEnv : Env :=
  [("+", .prim "+"), ("-", .prim "-"), ("*", .prim "*")]

def multnMod : GuardedMod where
  guard v := match v with | .num _ => true | _ => false
  handler v args := match v with
    | .num n =>
      let nums := args.filterMap (fun v => match v with | .num i => some i | _ => none)
      if nums.length == args.length
      then some (.num (nums.foldl (· * ·) n))
      else none
    | _ => none

def evalVal (mods : ModTable) (ptable : PolicyTable) (fuel : Nat) (level : Nat)
    (exp : Expr) (env : Env) (tower : TowerState) : Option Val :=
  (eval mods ptable fuel level exp env tower).map Prod.fst

-- Smoke tests
#eval evalVal [] [] 100 0 (.app [.var "+", .num 1, .num 2]) initEnv initTower

-- EM + install: modify rule for level 0
#eval evalVal [multnMod] [] 100 0
  (.ifte (.em (.install 0)) (.app [.num 2, .num 3, .num 4]) (.num 0))
  initEnv initTower

-- Nested EM: install at level 2
#eval evalVal [multnMod] [] 100 0 (.em (.em (.install 0))) initEnv initTower

-- REFLECTIVE GOVERNANCE: start with rejectAll, use EM to install acceptAll
-- at level 1, then install multn at level 1
-- (em (installPolicy 0)) replaces level 1's policy with acceptAllPolicy
-- (em (install 0)) then installs multn at level 1 (now accepted)
#eval evalVal [multnMod] [acceptAllPolicy] 100 0
  (.ifte (.em (.installPolicy 0))
    (.ifte (.em (.install 0))
      (.app [.num 2, .num 3, .num 4])
      (.num 0))
    (.num 0))
  initEnv guardedTower

-- Without the policy change, install is rejected
#eval evalVal [multnMod] [acceptAllPolicy] 100 0
  (.ifte (.em (.install 0))
    (.app [.num 2, .num 3, .num 4])
    (.num 0))
  initEnv guardedTower

/-
  Lemmas
-/

theorem conservative_refl (r : ApplyRule) : ConservativeExt r r :=
  fun _ _ _ h => h

theorem conservative_trans {r₁ r₂ r₃ : ApplyRule} :
    ConservativeExt r₁ r₂ → ConservativeExt r₂ r₃ → ConservativeExt r₁ r₃ :=
  fun h₁₂ h₂₃ v args res h => h₂₃ v args res (h₁₂ v args res h)

-- Pointwise conservative extension for towers
def TowerConservative (t₁ t₂ : TowerState) : Prop :=
  ∀ n, ConservativeExt (t₁ n).rule (t₂ n).rule

theorem tower_conservative_refl (t : TowerState) : TowerConservative t t :=
  fun n => conservative_refl (t n).rule

theorem tower_conservative_trans {t₁ t₂ t₃ : TowerState} :
    TowerConservative t₁ t₂ → TowerConservative t₂ t₃ → TowerConservative t₁ t₃ :=
  fun h₁₂ h₂₃ n => conservative_trans (h₁₂ n) (h₂₃ n)

theorem update_rule_conservative (t : TowerState) (n : Nat) (r : ApplyRule)
    (h : ConservativeExt (t n).rule r) :
    TowerConservative t (t.update n { (t n) with rule := r }) := by
  intro k
  by_cases hk : k = n
  · subst hk; simp [TowerState.update]; exact h
  · simp [TowerState.update, hk]; exact conservative_refl _

theorem update_policy_conservative (t : TowerState) (n : Nat) (p : Policy) :
    TowerConservative t (t.update n { (t n) with policy := p }) := by
  intro k
  by_cases hk : k = n
  · subst hk; simp [TowerState.update]; exact conservative_refl _
  · simp [TowerState.update, hk]; exact conservative_refl _

/-
  THEOREM 1: Tower safety.

  Same as before but with the richer tower state (rules + policies).
-/

-- Persistent soundness: governance is sound for any conservative
-- extension of the original tower, AND for any policy replacement
-- from the policy table.
-- SafeEvolution: all policies (in tower and in table) are universally sound.
-- Universal soundness is the key: it's preserved across rule changes.
def SafeEvolution (ptable : PolicyTable) (t : TowerState) : Prop :=
  (∀ n, (t n).policy.UnivSound) ∧ (∀ p, p ∈ ptable → p.UnivSound)

-- Helper: install preserves SafeEvolution
theorem install_safe (ptable : PolicyTable)
    (tower : TowerState) (level : Nat) (mod : GuardedMod)
    (h_safe : SafeEvolution ptable tower)
    (h_pass : (tower level).policy mod (tower level).rule = true) :
    let tower' := tower.update level { (tower level) with rule := applyMod mod (tower level).rule }
    TowerConservative tower tower' ∧ SafeEvolution ptable tower' := by
  constructor
  · exact update_rule_conservative tower level _ (h_safe.1 level (tower level).rule mod h_pass)
  · exact ⟨fun n => by
      by_cases hn : n = level
      · cases hn; simp [TowerState.update]; exact h_safe.1 level
      · simp [TowerState.update, hn]; exact h_safe.1 n,
    h_safe.2⟩

-- Helper: installPolicy preserves SafeEvolution if replacement is universally sound
theorem installPolicy_safe (ptable : PolicyTable)
    (tower : TowerState) (level : Nat) (newPolicy : Policy)
    (h_safe : SafeEvolution ptable tower)
    (h_univ : newPolicy.UnivSound) :
    let tower' := tower.update level { (tower level) with policy := newPolicy }
    TowerConservative tower tower' ∧ SafeEvolution ptable tower' := by
  exact ⟨update_policy_conservative tower level newPolicy,
    ⟨fun n => by
      by_cases hn : n = level
      · cases hn; simp [TowerState.update]; exact h_univ
      · simp [TowerState.update, hn]; exact h_safe.1 n,
    h_safe.2⟩⟩

mutual
theorem eval_tower_conservative (mods : ModTable) (ptable : PolicyTable)
    (fuel : Nat) (level : Nat) (exp : Expr) (env : Env)
    (tower : TowerState) (h_safe : SafeEvolution ptable tower)
    (v : Val) (tower' : TowerState) :
    eval mods ptable fuel level exp env tower = some (v, tower') →
    TowerConservative tower tower' ∧ SafeEvolution ptable tower' := by
  match fuel with
  | 0 => simp [eval]
  | n + 1 =>
    match exp with
    | .num _ | .bool _ | .lam _ _ =>
      simp only [eval]; intro h; obtain ⟨-, rfl⟩ := h
      exact ⟨tower_conservative_refl _, h_safe⟩
    | .var x =>
      simp only [eval]; intro h
      split at h <;> simp at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨tower_conservative_refl _, h_safe⟩
    | .ifte c t e =>
      simp only [eval]; intro h
      match hc : eval mods ptable n level c env tower with
      | none => simp [hc] at h
      | some (cv, tc) =>
        simp [hc] at h
        have ⟨htc, h_safe_c⟩ := eval_tower_conservative mods ptable n level c env
          tower h_safe cv tc hc
        match cv with
        | .bool false =>
          simp at h
          have ⟨hte, h_safe_e⟩ := eval_tower_conservative mods ptable n level e env
            tc h_safe_c v tower' h
          exact ⟨tower_conservative_trans htc hte, h_safe_e⟩
        | .bool true | .num _ | .closure _ _ _ | .prim _ =>
          simp at h
          have ⟨htt, h_safe_t⟩ := eval_tower_conservative mods ptable n level t env
            tc h_safe_c v tower' h
          exact ⟨tower_conservative_trans htc htt, h_safe_t⟩
    | .app exprs =>
      simp only [eval]; intro h
      match exprs with
      | [] => simp at h
      | f :: args =>
        simp only [eval] at h
        match hf : eval mods ptable n level f env tower with
        | none => simp [hf] at h
        | some (fv, tf) =>
          simp [hf] at h
          have ⟨htf, h_safe_f⟩ := eval_tower_conservative mods ptable n level f env
            tower h_safe fv tf hf
          match ha : evalList mods ptable n level args env tf with
          | none => simp [ha] at h
          | some (avs, ta) =>
            simp [ha] at h
            have ⟨hta, h_safe_a⟩ := evalList_tower_conservative mods ptable n level args env
              tf h_safe_f avs ta ha
            have h_fa := tower_conservative_trans htf hta
            match fv with
            | .closure params body cenv =>
              have ⟨htb, h_safe_b⟩ := eval_tower_conservative mods ptable n level body
                (Env.extend cenv params avs) ta h_safe_a v tower' h
              exact ⟨tower_conservative_trans h_fa htb, h_safe_b⟩
            | .num _ | .bool _ | .prim _ =>
              simp at h; split at h <;> simp at h
              obtain ⟨-, rfl⟩ := h; exact ⟨h_fa, h_safe_a⟩
    -- EM: level-shift
    | .em body =>
      simp only [eval]; intro h
      exact eval_tower_conservative mods ptable n (level + 1) body env
        tower h_safe v tower' h
    -- INSTALL: modify rule, governed by policy
    | .install modIdx =>
      simp only [eval]; intro h
      split at h
      · next mod _ =>
        split at h
        · next h_pass =>
          obtain ⟨-, rfl⟩ := h
          exact install_safe ptable tower level mod h_safe h_pass
        · obtain ⟨-, rfl⟩ := h; exact ⟨tower_conservative_refl _, h_safe⟩
      · obtain ⟨-, rfl⟩ := h; exact ⟨tower_conservative_refl _, h_safe⟩
    -- INSTALL POLICY: replace policy (governance is reflective!)
    | .installPolicy polIdx =>
      simp only [eval]; intro h
      split at h
      · next newPolicy h_mem =>
        obtain ⟨-, rfl⟩ := h
        have h_in : newPolicy ∈ ptable := List.mem_of_getElem? h_mem
        exact installPolicy_safe ptable tower level newPolicy h_safe
          (h_safe.2 newPolicy h_in)
      · obtain ⟨-, rfl⟩ := h; exact ⟨tower_conservative_refl _, h_safe⟩
termination_by fuel

theorem evalList_tower_conservative (mods : ModTable) (ptable : PolicyTable)
    (fuel : Nat) (level : Nat) (exps : List Expr) (env : Env)
    (tower : TowerState) (h_safe : SafeEvolution ptable tower)
    (vs : List Val) (tower' : TowerState) :
    evalList mods ptable fuel level exps env tower = some (vs, tower') →
    TowerConservative tower tower' ∧ SafeEvolution ptable tower' := by
  match fuel with
  | 0 => simp [evalList]
  | n + 1 =>
    match exps with
    | [] =>
      simp only [evalList]; intro h; obtain ⟨-, rfl⟩ := h
      exact ⟨tower_conservative_refl _, h_safe⟩
    | e :: rest =>
      simp only [evalList]; intro h
      match he : eval mods ptable n level e env tower with
      | none => simp [he] at h
      | some (val, te) =>
        simp [he] at h
        have ⟨hte, h_safe_e⟩ := eval_tower_conservative mods ptable n level e env
          tower h_safe val te he
        match hr : evalList mods ptable n level rest env te with
        | none => simp [hr] at h
        | some (vs', tr) =>
          simp [hr] at h; obtain ⟨-, rfl⟩ := h
          have ⟨htr, h_safe_r⟩ := evalList_tower_conservative mods ptable n level rest env
            te h_safe_e vs' tr hr
          exact ⟨tower_conservative_trans hte htr, h_safe_r⟩
termination_by fuel
end

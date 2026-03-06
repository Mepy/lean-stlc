open Nat

inductive Exp : Type where
  | var : Nat -> Exp
  | lam : Exp -> Exp
  | app : Exp -> Exp -> Exp
  | unit : Exp
  | pair : Exp -> Exp -> Exp
  | fst : Exp -> Exp
  | snd : Exp -> Exp
  | inl : Exp -> Exp
  | inr : Exp -> Exp
  | case : Exp -> Exp -> Exp -> Exp
deriving Repr


/-- var-A mapping is a function from variable indices to As
 -- A = Exp for substitution
 -- A = Nat for renaming
 --/
@[simp]
def cons {A : Type} (x : A) (ξ : Nat → A) : Nat → A
  | 0 => x
  | n + 1 => ξ n
infixr:50 "+:" => cons

def Renaming := Nat -> Nat
def Substitution := Nat -> Exp


/-- 0 +: (fun n => (ξ n) + 1)
 -- 0 ↦ 0
 -- n + 1 ↦ (ξ n) + 1
 --/
def lift (ξ : Renaming) : Renaming :=
  0 +: (succ ∘ ξ)


/-- Extensional Equalities -/
theorem liftExt : ∀ ξ ξ', (∀ n, ξ n = ξ' n) → ∀ n, lift ξ n = lift ξ' n
  | ξ, ξ', h, 0 => by simp [lift]
  | ξ, ξ', h, n + 1 => by simp [lift, h]

theorem liftId : ∀ n, lift id n = id n
  | 0 => by simp [lift]
  | n + 1 => by simp [lift]

theorem liftComp ξ ζ ς : (∀ n , (ξ ∘ ζ) n = ς n) →
  ∀ n, (lift ξ ∘ lift ζ) n = (lift ς) n
  | h, 0 => by simp [lift]
  | h, n + 1 => by simp [lift]; apply h

/-- (lift ξ ∘ succ) n = lift ξ (n + 1) = (ξ n) + 1 = (succ ∘ ξ) n -/
theorem liftSucc ξ n : (lift ξ ∘ succ) n = (succ ∘ ξ) n
  := by simp [lift]

/-- rename -/
@[simp]
def rename (ξ : Renaming) : Exp -> Exp
  | .var n => .var (ξ n) -- var n ↦ var (ξ n), renaming variables
  | .lam e => .lam (rename (lift ξ) e) -- lifting ξ to account for the new binder
  | .app e1 e2 => .app (rename ξ e1) (rename ξ e2)
  | .unit => .unit
  | .pair e1 e2 => .pair (rename ξ e1) (rename ξ e2)
  | .fst e => .fst (rename ξ e)
  | .snd e => .snd (rename ξ e)
  | .inl e => .inl (rename ξ e)
  | .inr e => .inr (rename ξ e)
  | .case e0 e1 e2 => .case (rename ξ e0) (rename (lift ξ) e1) (rename (lift ξ) e2) -- lifting ξ to account for the new binder

/-- rename succ : Substitution
 -- is to rename variables by adding 1 to their indices, i.e., var n ↦ var (n + 1)
 -- or written as succSubst : Substitution := rename succ
 --/
example : ∀ n, rename succ (.var n) = .var (n + 1) := by simp [rename]



/-- we only prove the following case-by-case, we will use more tactics for shorter proofs -/
theorem renameExt ξ ξ' (h : ∀ n, ξ n = ξ' n) :
  ∀ e,  rename ξ e = rename ξ' e
  | .var n => by simp [rename, h]
  | .lam e => by
    simp [rename]
    apply renameExt
    apply liftExt
    exact h
  | .app e1 e2 => by
    simp [rename]
    apply And.intro
    apply renameExt; exact h
    apply renameExt; exact h
  | .unit => by simp [rename]
  | .pair e1 e2 => by
    simp [rename]
    apply And.intro
    apply renameExt; exact h
    apply renameExt; exact h
  | .fst e => by
    simp [rename]
    apply renameExt
    exact h
  | .snd e => by
    simp [rename]
    apply renameExt
    exact h
  | .inl e => by
    simp [rename]
    apply renameExt
    exact h
  | .inr e => by
    simp [rename]
    apply renameExt
    exact h
  | .case e0 e1 e2 => by
    simp [rename]
    apply And.intro
    /- e0 -/
    apply renameExt; exact h
    apply And.intro
    /- e1 -/
    apply renameExt; apply liftExt; exact h
    /- e2 -/
    apply renameExt; apply liftExt; exact h

theorem renameId : ∀ e, rename id e = e := by
  intros e
  induction e <;> simp [rename]
  all_goals repeat' constructor /- And.intro -/
  all_goals try assumption
  all_goals try (rw [renameExt (lift id) id]; assumption; apply liftId)

/-- (rename ξ ∘ rename ζ) = rename (ξ ∘ ζ) -/
theorem renameComp ξ ζ ς : (∀ n , (ξ ∘ ζ) n = ς n) →
  ∀ e, rename ξ (rename ζ e) = rename ς e := by
  intros h e
  induction e generalizing ξ ζ ς /- for lifting in lam and case, which requires theorem on (lift ξ ∘ lift ζ) = lift ς -/
  all_goals simp [rename]
  all_goals repeat' constructor /- And.intro -/
  all_goals try apply_rules [liftComp]

/-- up is to lift substitution
 -- .var 0 +: (fun n => rename succ (σ n) )
 -- 0 ↦ .var 0
 -- n + 1 ↦ rename succ (σ n)
 --/
def up (σ : Substitution) : Substitution :=
  .var 0 +: (rename succ ∘ σ)
prefix:95 "⇑" => up

theorem upExt : ∀ σ σ', (∀ n, σ n = σ' n) → ∀ n, up σ n = up σ' n
  | σ, σ', h, 0 => by simp [up]
  | σ, σ', h, n + 1 => by simp [up, h]

theorem upId (σ : Substitution) : (∀ n , σ n = .var n ) -> ∀ n, (⇑ σ) n = .var n
  | h, 0 => by simp [up]
  | h, n + 1 => by simp [up]; rw [h]; simp [rename]

/-- ⇑ σ ∘ succ = (rename succ) ∘ σ
 -- analogue to liftSucc,
 -- (up σ ∘ succ) n = up σ (n + 1) = rename succ (σ n) = (rename succ ∘ σ) n

 -- another proof := fun n => rfl
 --/
theorem upSucc σ : ∀ n , (⇑ σ ∘ succ) n = (rename succ ∘ σ) n
  := by simp [up]



/-- extensional, ⇑ σ ∘ lift ξ = ⇑ (σ ∘ ξ) -/
theorem upLift ξ σ τ (h : ∀ n, (σ ∘ ξ) n = τ n) : ∀ n, (⇑ σ ∘ lift ξ) n = (⇑ τ) n
  | 0 => by simp [lift, up]
  | n + 1 => by simp [lift, up, <- h]

/-- extensional, .var ∘ lift ξ = ⇑ (.var ∘ ξ) -/
theorem upVar ξ : ∀ n, (.var ∘ lift ξ) n = (⇑ (.var ∘ ξ)) n
  | 0 => by simp [lift, up]
  | n + 1 => by simp [lift, up, rename]

/-- extensional, rename (lift ξ) ∘ ⇑ σ = ⇑ (rename ξ ∘ σ) -/
theorem upRename ξ σ τ (h : ∀ n, (rename ξ ∘ σ) n = τ n)
: ∀ n, (rename (lift ξ) ∘ ⇑ σ) n = (⇑ τ) n
  | 0 => by simp [up, lift, rename]
  | n + 1 => by calc
      (rename (lift ξ) ∘ ⇑ σ) (n + 1)
      = (rename (lift ξ) ∘ rename succ) (σ n) := by simp [up, lift]
    _ = rename (lift ξ ∘ succ) (σ n) := by simp [renameComp (lift ξ) succ (lift ξ ∘ succ)]
    _ = (rename (succ ∘ ξ)) (σ n) := by rfl
    _ = (rename succ ∘ rename ξ) (σ n) := by simp [<- renameComp succ ξ (succ ∘ ξ)]
    _ = rename succ ((rename ξ ∘ σ) n) := by rfl
    _ = rename succ (τ n) := by rw [(h n)]
    _ = (⇑ τ) (n + 1) := by simp [up]

/-- substitute -/
@[simp]
def subst (σ : Substitution) : Exp -> Exp
  | .var n => σ n -- var n ↦ σ n, substituting variables
  | .lam e => .lam (subst (⇑ σ) e) -- lifting σ to account for the new binder
  | .app e1 e2 => .app (subst σ e1) (subst σ e2)
  | .unit => .unit
  | .pair e1 e2 => .pair (subst σ e1) (subst σ e2)
  | .fst e => .fst (subst σ e)
  | .snd e => .snd (subst σ e)
  | .inl e => .inl (subst σ e)
  | .inr e => .inr (subst σ e)
  | .case e0 e1 e2 => .case (subst σ e0) (subst (⇑ σ) e1) (subst (⇑ σ) e2) -- lifting σ to account for the new binder

notation:70 e "⦃" σ "⦄" => subst σ e
notation:50 "⟨⟩" => Exp.var
notation:50 "⟨" e "⟩" => e +: Exp.var
example (e) : (.var 0) ⦃ ⟨e⟩ ⦄ = e := by simp [subst]

/-- analogue to renameExt
 -- we only prove the following case-by-case, we will use more tactics for shorter proofs
 --/
theorem substExt σ σ' (h : ∀ n, σ n = σ' n) :
  ∀ e, e ⦃ σ ⦄ = e ⦃ σ' ⦄
  | .var n => by simp [subst, h]
  | .lam e => by
    simp [subst]
    apply substExt
    apply upExt
    exact h
  | .app e1 e2 => by
    simp [subst]
    apply And.intro
    apply substExt; exact h
    apply substExt; exact h
  | .unit => by simp [subst]
  | .pair e1 e2 => by
    simp [subst]
    apply And.intro
    apply substExt; exact h
    apply substExt; exact h
  | .fst e => by
    simp [subst]
    apply substExt
    exact h
  | .snd e => by
    simp [subst]
    apply substExt
    exact h
  | .inl e => by
    simp [subst]
    apply substExt
    exact h
  | .inr e => by
    simp [subst]
    apply substExt
    exact h
  | .case e0 e1 e2 => by
    simp [subst]
    apply And.intro
    /- e0 -/
    apply substExt; exact h
    apply And.intro
    /- e1 -/
    apply substExt; apply upExt; exact h
    /- e2 -/
    apply substExt; apply upExt; exact h

theorem substId σ (h :∀ n , σ n = .var n ) :
  ∀ e, e ⦃ σ ⦄ = e
  := by
  intros e; induction e
    generalizing σ
    /- for lifting in lam and case, which requires theorem on (up σ) n = .var n -/
  all_goals simp [subst]
  all_goals repeat' constructor /- And.intro -/
  all_goals try assumption
  all_goals apply_rules [upId]

/-- extensional, (rename ξ e) ⦃ σ ⦄ = e ⦃ σ ∘ ξ ⦄ -/
theorem substRename ξ σ τ (h : ∀ n, (σ ∘ ξ) n = τ n) :
  ∀ e, (rename ξ e) ⦃ σ ⦄ = e ⦃ τ ⦄
  := by
  intros e; induction e
    generalizing ξ σ τ
    /- for lifting in lam and case, which requires theorem on (⇑ σ ∘ lift ξ) n = (⇑ τ) n -/
  all_goals simp [subst, rename]
  all_goals repeat' constructor /- And.intro -/
  all_goals try apply_rules [upLift, upRename, upVar]

theorem renameSubst ξ σ τ (h : ∀ n, (rename ξ ∘ σ) n = τ n) :
  ∀ e, rename ξ (e ⦃ σ ⦄) = e ⦃ τ ⦄
  := by
  intros e; induction e
    generalizing ξ σ τ
    /- for lifting in lam and case, which requires theorem on (rename (lift ξ) ∘ ⇑ σ) n = (⇑ τ) n) -/
  all_goals simp [subst, rename]
  all_goals repeat' constructor /- And.intro -/
  all_goals try apply_rules [upLift, upRename, upVar]


theorem upSubst ρ σ τ (h : ∀ n, (subst ρ ∘ σ) n = τ n) :
  ∀ n, (subst (⇑ ρ) ∘ (⇑ σ)) n = (⇑ τ) n
  | 0 => by simp [up]
  | n + 1 => by calc
        (subst (⇑ ρ) ∘ (⇑ σ)) (n + 1)
    _ = (subst (⇑ ρ) ∘ rename succ) (σ n) := by simp [up]
    _ = (rename succ (σ n)) ⦃ ⇑ ρ ⦄ := by rfl
    _ = (σ n) ⦃ (⇑ ρ) ∘ succ ⦄ := by simp [substRename succ (⇑ ρ) ((⇑ ρ) ∘ succ)]
    _ = (σ n) ⦃ rename succ ∘ ρ ⦄ := by rfl -- due to (⇑ ρ) ∘ succ = fun n => (⇑ p) (succ n) = fun n => rename succ (p n) = rename succ ∘ p
    _ = rename succ ((σ n) ⦃ ρ ⦄) := by simp [<-renameSubst succ ρ (rename succ ∘ ρ)]
    _ = rename succ ((subst ρ ∘ σ) n) := by rfl
    _ = rename succ (τ n) := by rw [h]
    _ = (⇑ τ) (n + 1) := by simp [up]

/-- extensional, (subst ρ ∘ subst σ) = subst (subst ρ ∘ σ) -/
theorem substComp ρ σ τ (h : ∀ n, (subst ρ ∘ σ) n = τ n) :
  ∀ e, e ⦃ σ ⦄ ⦃ ρ ⦄ = e ⦃ τ ⦄
  := by
  intros e; induction e
    generalizing ρ σ τ
    /- for lifting in lam and case, which requires theorem on (subst (⇑ ρ) ∘ (⇑ σ)) n = (⇑ τ) n -/
  all_goals simp [subst]
  all_goals repeat' constructor /- And.intro -/
  all_goals try apply_rules [upSubst]


theorem substSuccSingleton (e a : Exp) : rename succ e ⦃⟨ a ⟩⦄ = e
  := by
  rw [substRename succ (⟨ a ⟩) .var]
  apply substId
  all_goals simp

theorem substCons σ a :
  ∀ e, e ⦃ ⇑ σ ⦄ ⦃⟨ a ⟩⦄ = e ⦃ a +: σ ⦄
  := by
  intros e
  rw [substComp (⟨ a ⟩) (⇑ σ) _ (λ n => rfl)]
  apply substExt
  intros n; cases n <;> simp [up, subst]
  apply substSuccSingleton

theorem renameIsSubst ξ : ∀ e, rename ξ e = e ⦃ .var ∘ ξ ⦄
  := by
  intros e; cases e
  all_goals simp [subst, rename]
  all_goals repeat' constructor /- And.intro -/
  all_goals try apply renameIsSubst ξ
  all_goals try (
    rw [renameIsSubst (lift ξ)]
    rw [substExt]
    apply upVar ξ
  )

import LeanStlc.Syntax
import LeanStlc.Typing
import LeanStlc.Evaluation

section

set_option hygiene false

notation:70 "⟦" A:41 "⟧" "∋" v:70 => 𝒱 A v
notation:70 "ℰ⟦" A:41 "⟧" "∋" e:70 => ℰ A e
notation:70 "⟦" Γ:41 "⟧" "∋" σ:70 => wfSubst Γ σ
notation:40 Γ:41 "⊨"  e:41 "∶" A:41 => semTyp Γ e A

mutual
@[simp]
def 𝒱 : Typ -> Exp -> Prop
  | .unit, .unit => True
  | .arr A B, .lam e => ∀ v,  ⟦ A ⟧ ∋ v -> ℰ⟦ B ⟧ ∋ (e ⦃ ⟨v⟩ ⦄)
  | .prod A1 A2, .pair e1 e2 => ⟦ A1 ⟧ ∋ e1 ∧ ⟦ A2 ⟧ ∋ e2
  | .sum A1 _, .inl e => ⟦ A1 ⟧ ∋ e
  | .sum _ A2, .inr e => ⟦ A2 ⟧ ∋ e
  | _, _ => False

@[simp]
def ℰ : Typ -> Exp -> Prop
  | A, e => ∃ v, ⟦ A ⟧ ∋ v ∧ e ⟶* v
end

def wfSubst : Ctx -> Substitution -> Prop
  | ⬝, σ => ∀ n, σ n = .var n
  | Γ ∷ A, σ => ∃ (σ' : Substitution) (a : Exp) ,
      ⟦ Γ ⟧ ∋ σ'
    ∧ ⟦ A ⟧ ∋ a
    ∧ ∀ n, σ n = (a +: σ') n
def semTyp (Γ : Ctx) e A := ∀ σ, ⟦ Γ ⟧ ∋ σ -> ℰ⟦ A ⟧ ∋ e ⦃ σ ⦄
end

/-- .var is identity substitution on the empty context -/
def wfvar : ⟦ (⬝ : Ctx) ⟧ ∋ .var
  := by simp [wfSubst]

/-- cons(`LeanStlc.Syntax.cons`, $+:$ ) to extend a substitution -/
def wfcons : ∀ {Γ : Ctx} {σ} {A : Typ} {a : Exp},
  ⟦ Γ ⟧ ∋ σ ->
  ⟦ A ⟧ ∋ a ->
  -----------------------------
  ⟦ Γ ∷ A ⟧ ∋ (a +: σ)
  | Γ, σ, A, a, wfσ, wfa => by
    unfold wfSubst
    exists σ
    exists a
    apply And.intro wfσ
    apply And.intro wfa
    intros n; cases n <;> simp

/-- obtain the semantics of variable n -/
def wfIn {Γ : Ctx} {σ} {n} {A} :
  ⟦ Γ ⟧ ∋ σ ->
  Γ ∋ n ∶ A ->
  ⟦ A ⟧ ∋ σ n
  | wfσ, Ctx.In.here => by
    unfold wfSubst at wfσ
    let ⟨ σ', a, wσ', wa, eq ⟩ := wfσ
    rw [eq]
    exact wa
  | wfσ, Ctx.In.there wte => by
    unfold wfSubst at wfσ
    let ⟨ σ', a, wσ', wa, eq ⟩ := wfσ
    rw [eq]
    apply wfIn wσ' wte

/-! we use `invUnit`, `invArr`, `invProd`, `invSum` to do inversion
  when we know the the type $A$ in the logical relation $⟦ A ⟧ ∋ v$,
  which will be used in the proof of elimination forms
  (e.g. .app, .fst, .snd, .case) in the `fundamental` theorem.
 -/
def invUnit {v : Exp} (wfv : ⟦ .unit ⟧ ∋ v) : v = .unit
  := by cases v <;> simp at wfv <;> simp

def invArr {A B : Typ} {v : Exp}
  (wfv : ⟦.arr A B ⟧ ∋ v) :
  ∃ e, v = .lam e ∧ ∀ a, ⟦ A ⟧ ∋ a -> ℰ⟦ B ⟧ ∋ (e ⦃ ⟨a⟩ ⦄)
  := by
    cases v <;> simp at wfv
    case lam => unfold ℰ ; exact ⟨_, rfl, wfv⟩

def invProd {A1 A2 : Typ} {v : Exp}
  (wfv : ⟦.prod A1 A2 ⟧ ∋ v) :
  ∃ v1 v2, v = .pair v1 v2 ∧ ⟦ A1 ⟧ ∋ v1 ∧ ⟦ A2 ⟧ ∋ v2
  := by
    cases v <;> simp at wfv
    case pair v1 v2 => exists v1; exists v2

def invSum {A1 A2 : Typ} {v : Exp}
  (wfv : ⟦.sum A1 A2 ⟧ ∋ v) :
  (∃ v1, v = .inl v1 ∧ ⟦ A1 ⟧ ∋ v1) ∨ (∃ v2, v = .inr v2 ∧ ⟦ A2 ⟧ ∋ v2)
  := by
    cases v <;> simp at wfv
    case inl v1 => left; exists v1
    case inr v2 => right; exists v2

/-! the most important cases are .app and .lam,
    and also the .case is a bit similar to .lam when interacting with variables binding.
 -/
theorem fundamental {Γ} {e : Exp} {A : Typ} (wte : Γ ⊢ e ∶ A)
  : Γ ⊨ e ∶ A
  := fun (σ) (wfσ : ⟦ Γ ⟧ ∋ σ) => -- to show ℰ⟦ A ⟧ ∋ e ⦃ σ ⦄
  match e, A, wte with
  | .var n, _, .var wte => by
    have wfe := wfIn wfσ wte
    simp [ℰ]
    exists (σ n)
  | .app e1 e2, B, .app wte1 wte2 => by
    have wfe1 : ℰ⟦ .arr _ B ⟧ ∋ e1 ⦃ σ ⦄
      := fundamental wte1 σ wfσ
    have wfe2 : ℰ⟦ _ ⟧ ∋ e2 ⦃ σ ⦄
      := fundamental wte2 σ wfσ
    simp [ℰ] at wfe1 wfe2
    let ⟨ v1, wfv1, red1 ⟩ := wfe1
    let ⟨ v2, wfv2, red2 ⟩ := wfe2
    let ⟨ e, eq, h ⟩ := invArr wfv1
    let wf := h v2 wfv2
    simp [ℰ] at wf
    let ⟨ v, wfv, red3 ⟩:= wf
    unfold ℰ
    exists v
    apply And.intro wfv
    simp [subst]
    calc
        e1⦃σ⦄.app (e2⦃σ⦄)
        ⟶* v1.app (e2⦃σ⦄) := Evals.app1 red1
      _ ⟶* v1.app v2 := Evals.app2 red2
      _ = (Exp.lam e).app v2 := by rw [eq]
      _ ⟶ e ⦃ ⟨ v2⟩ ⦄ := by apply Eval.appLam
      _ ⟶* v := red3
  | .lam e, .arr A B, .lam wte => by
    unfold ℰ
    exists (.lam e⦃σ⦄)
    apply And.intro _ (Evals.refl)
    simp [𝒱]
    intros a wfa
    have wfe := fundamental wte (a+:σ) (wfcons wfσ wfa)
    simp [ℰ] at wfe
    let ⟨ v, wfv, red ⟩ := wfe
    exists v
    apply And.intro wfv
    calc
      e⦃⇑ σ⦄⦃⟨ a ⟩⦄
      _ = e⦃a+:σ⦄ := by apply substCons
      _ ⟶* v := red
  | .unit, .unit, .unit => by
    unfold ℰ
    exists .unit
    apply And.intro _ (Evals.refl)
    simp [𝒱]
  | .pair e1 e2, .prod A1 A2, .pair wte1 wte2 => by
    have wfe1 := fundamental wte1 σ wfσ
    have wfe2 := fundamental wte2 σ wfσ
    simp [ℰ] at wfe1 wfe2
    let ⟨ v1, wfv1, red1 ⟩ := wfe1
    let ⟨ v2, wfv2, red2 ⟩ := wfe2
    unfold ℰ
    exists (.pair v1 v2)
    apply And.intro
    simp [𝒱]
    apply And.intro wfv1 wfv2
    calc
        (.pair e1 e2)⦃σ⦄
        =   .pair (e1⦃σ⦄) (e2⦃σ⦄) := by simp [subst]
      _ ⟶* .pair v1 (e2⦃σ⦄) := by apply Evals.pair1 red1
      _ ⟶* .pair v1 v2 := by apply Evals.pair2 red2
  | .fst e, A1, .fst wte => by
    have wfe := fundamental wte σ wfσ
    simp [ℰ] at wfe
    let ⟨ v, wfv, red ⟩ := wfe
    let ⟨ v1, v2, eq, wfv1, wfv2 ⟩ := invProd wfv

    unfold ℰ
    exists v1
    apply And.intro wfv1
    calc
        (.fst e)⦃σ⦄
        =   .fst (e⦃σ⦄) := by simp [subst]
      _ ⟶* .fst v := by apply Evals.fst red
      _ = .fst (.pair v1 v2) := by rw [eq]
      _ ⟶ v1 := by apply Eval.fstPair
  | .snd e, A2, .snd wte => by
    have wfe := fundamental wte σ wfσ
    simp [ℰ] at wfe
    let ⟨ v, wfv, red ⟩ := wfe
    let ⟨ v1, v2, eq, wfv1, wfv2 ⟩ := invProd wfv

    unfold ℰ
    exists v2
    apply And.intro wfv2
    calc
        (.snd e)⦃σ⦄
        =   .snd (e⦃σ⦄) := by simp [subst]
      _ ⟶* .snd v := by apply Evals.snd red
      _ = .snd (.pair v1 v2) := by rw [eq]
      _ ⟶ v2 := by apply Eval.sndPair
  | .inl e1, .sum A1 A2, .inl wte1 => by
    have wfe1 := fundamental wte1 σ wfσ
    simp [ℰ] at wfe1
    let ⟨ v1, wfv1, red1 ⟩ := wfe1
    unfold ℰ
    exists (.inl v1)
    apply And.intro
    simp [𝒱]
    exact wfv1
    calc
        (.inl e1)⦃σ⦄
        =   .inl (e1⦃σ⦄) := by simp [subst]
      _ ⟶* .inl v1 := by apply Evals.inl red1
  | .inr e2, .sum A1 A2, .inr wte2 => by
    have wfe2 := fundamental wte2 σ wfσ
    simp [ℰ] at wfe2
    let ⟨ v2, wfv2, red2 ⟩ := wfe2
    unfold ℰ
    exists (.inr v2)
    apply And.intro
    simp [𝒱]
    exact wfv2
    calc
        (.inr e2)⦃σ⦄
        =   .inr (e2⦃σ⦄) := by simp [subst]
      _ ⟶* .inr v2 := by apply Evals.inr red2

  | .case e0 e1 e2, C, .case wte0 wte1 wte2 => by
    have wfe0 := fundamental wte0 σ wfσ
    simp [ℰ] at wfe0
    let ⟨ v0, wfv0, red0 ⟩ := wfe0
    let inv := invSum wfv0
    match inv with
    | Or.inl ⟨ v1, eq, wfv1 ⟩ =>
      have wfe := fundamental wte1 (v1+:σ) (wfcons wfσ wfv1)
      simp [ℰ] at wfe
      let ⟨ v, wfv, red ⟩ := wfe
      unfold ℰ
      exists v
      apply And.intro wfv
      calc
          (.case e0 e1 e2)⦃σ⦄
          =   .case (e0⦃σ⦄) (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by simp [subst]
        _ ⟶* .case v0 (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by apply Evals.case0 red0
        _ ⟶* .case (.inl v1) (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by rw [eq]
        _ ⟶ e1 ⦃⇑ σ⦄ ⦃⟨ v1 ⟩⦄ := by apply Eval.caseInl
        _ = e1⦃v1+:σ⦄ := by apply substCons
        _ ⟶* v := red
    | Or.inr ⟨ v2, eq, wfv2 ⟩ =>
      have wfe := fundamental wte2 (v2+:σ) (wfcons wfσ wfv2)
      simp [ℰ] at wfe
      let ⟨ v, wfv, red ⟩ := wfe
      unfold ℰ
      exists v
      apply And.intro wfv
      calc
          (.case e0 e1 e2)⦃σ⦄
          =   .case (e0⦃σ⦄) (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by simp [subst]
        _ ⟶* .case v0 (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by apply Evals.case0 red0
        _ ⟶* .case (.inr v2) (e1⦃⇑ σ⦄) (e2⦃⇑ σ⦄) := by rw [eq]
        _ ⟶ e2 ⦃⇑ σ⦄ ⦃⟨ v2 ⟩⦄ := by apply Eval.caseInr
        _ = e2⦃v2+:σ⦄ := by apply substCons
        _ ⟶* v := red

theorem safety {e : Exp} {A : Typ} (wte : ⬝ ⊢ e ∶ A)
  : ∃ v, ⟦ A ⟧ ∋ v ∧ e ⟶* v
  := by
    let wfe := fundamental wte .var wfvar
    simp [ℰ] at wfe
    let ⟨ v, wfv, red ⟩ := wfe
    exists v
    apply And.intro wfv
    calc
      e = e⦃⟨⟩⦄ := by simp [substId]
      _ ⟶* v := red

example {e : Exp} (wte : ⬝ ⊢ e ∶ .unit)
  : e ⟶* .unit
  := by
    let wfe := fundamental wte .var wfvar
    let ⟨ v, wfv, proof ⟩ := safety wte
    let eq := invUnit wfv
    rw [eq] at proof
    exact proof

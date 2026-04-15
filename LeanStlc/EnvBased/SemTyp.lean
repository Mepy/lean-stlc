import LeanStlc.EnvBased.Syntax
import LeanStlc.EnvBased.DynSem
import LeanStlc.EnvBased.SynTyp
import LeanStlc.EnvBased.LogRel

namespace EnvOf

theorem nil :
  𝓖⟦ ⬝ ⟧ ∋ []
  := by simp [EnvOf]
theorem cons {Γ γ v A} :
  𝓖⟦ Γ ⟧ ∋ γ ->
  𝓥⟦ A ⟧ ∋ v ->
  𝓖⟦ Γ ; A ⟧ ∋ γ ∷ v
  := fun 𝓖γ 𝓥v => by
  simp [EnvOf] at *
  refine ⟨ 𝓖γ , 𝓥v ⟩

theorem Has :
  𝓖⟦ Γ ⟧ ∋ γ ->
  Γ ∋ x ∶ A ->
  ∃ v,
    𝓥⟦ A ⟧ ∋ v
  ∧ γ ∋ x ⇒ v
  | 𝓖γ, .here => by
    rename_i Γ
    rcases γ <;> simp [EnvOf] at 𝓖γ
    rename_i γ v
    rcases 𝓖γ with ⟨ 𝓖γ, 𝓥v ⟩
    refine ⟨ v , 𝓥v , .here ⟩
  | 𝓖γ, .there h => by
    rename_i Γ A' x
    rcases γ <;> simp [EnvOf] at 𝓖γ
    rename_i γ v'
    rcases 𝓖γ with ⟨ 𝓖γ, 𝓥v' ⟩
    rcases Has 𝓖γ h with ⟨v, 𝓥v, γHasx⟩
    refine ⟨ v , 𝓥v , .there γHasx ⟩

end EnvOf

namespace SemTyp

theorem int {Γ n} :
  Γ ⊨ .int n ∶ .int := by
  simp [SemTyp]
  intros
  unfold ExpOf
  refine ⟨ .int n , ?_, ?_ ⟩
  simp [ValOf]
  simp [Eval.int]

theorem env {Γ ξ Ξ} :
  ⊨ ξ ∶ Ξ ->
  Γ ⊨ .env ξ ∶ .ctx Ξ := by
  intro 𝓖ξ
  simp [SemTyp]
  intros
  unfold ExpOf
  refine ⟨ .env ξ , ?_, ?_ ⟩
  simp [ValOf, 𝓖ξ]
  simp [Eval.env]

theorem cur {Γ} :
  Γ ⊨ .cur ∶ .ctx Γ := by
  simp [SemTyp]
  intros γ 𝓖γ
  unfold ExpOf
  refine ⟨ .env γ , ?_, ?_ ⟩
  simp [ValOf, 𝓖γ]
  simp [Eval.cur]




theorem get {Γ Ξ eξ x A} :
  Γ ⊨ eξ ∶ .ctx Ξ ->
  Ξ ∋ x ∶ A ->
  Γ ⊨ .get eξ x ∶ A := by
  intro wteξ ΞHasx
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases wteξ γ 𝓖γ with ⟨ vξ, 𝓖ξ, evξ ⟩
  rcases vξ <;> simp [ValOf] at 𝓖ξ
  rename_i ξ
  rcases EnvOf.Has 𝓖ξ ΞHasx with ⟨ v, 𝓥v, ξHasx ⟩
  refine ⟨ v, 𝓥v, ?_ ⟩
  apply Eval.get evξ ξHasx

theorem clos {Γ Ξ eξ e A B} :
  Γ ⊨ eξ ∶ .ctx Ξ ->
  Ξ ; A ⊨ e ∶ B ->
  Γ ⊨ .clos eξ e ∶ .arr A B := by
  intro heξ he
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at heξ ⊢
  rcases heξ γ 𝓖γ with ⟨eξ, 𝓖ξ, evξ⟩
  rcases eξ <;> simp [ValOf] at 𝓖ξ
  rename_i ξ
  refine ⟨ .clos (.env ξ) e , ?_, ?_ ⟩

  simp [ValOf]
  intros v 𝓥v
  apply he (ξ∷v) (EnvOf.cons 𝓖ξ 𝓥v)

  apply Eval.clos evξ

theorem app {Γ e1 e2 A B} :
  Γ ⊨ e1 ∶ .arr A B ->
  Γ ⊨ e2 ∶ A ->
  Γ ⊨ .app e1 e2 ∶ B := by
  intro he1 he2
  simp [SemTyp] at *
  unfold ExpOf at *
  intros γ 𝓖γ
  rcases he1 γ 𝓖γ with ⟨v1, 𝓥v1, ev1⟩
  rcases he2 γ 𝓖γ with ⟨v2, 𝓥v2, ev2⟩
  rcases v1 <;> try simp [ValOf] at 𝓥v1
  rename_i eξ e
  rcases eξ <;> try simp [ValOf] at 𝓥v1
  rename_i ξ
  unfold ExpOf at *
  rcases 𝓥v1 v2 𝓥v2 with ⟨v, 𝓥v, ev⟩
  refine ⟨ v , 𝓥v, ?_ ⟩
  apply Eval.app ev1 ev2 ev

theorem letin {Γ e1 e2 A B} :
  Γ ⊨ e1 ∶ A ->
  Γ ; A ⊨ e2 ∶ B ->
  Γ ⊨ .letin e1 e2 ∶ B := by
  intro he1 he2
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he1 γ 𝓖γ with ⟨v1, 𝓥v1, ev1⟩
  rcases he2 (γ∷v1) (EnvOf.cons 𝓖γ 𝓥v1) with ⟨v2, 𝓥v2, ev2⟩
  refine ⟨ v2 , 𝓥v2, ?_ ⟩
  apply Eval.letin ev1 ev2

theorem unit {Γ} :
  Γ ⊨ .unit ∶ .unit := by
  simp [SemTyp]
  intros
  unfold ExpOf
  refine ⟨ .unit , ?_, ?_ ⟩
  simp [ValOf]
  simp [Eval.unit]

theorem pair {Γ e1 e2 A B} :
  Γ ⊨ e1 ∶ A ->
  Γ ⊨ e2 ∶ B ->
  Γ ⊨ .pair e1 e2 ∶ .prod A B := by
  intro he1 he2
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he1 γ 𝓖γ with ⟨v1, 𝓥v1, ev1⟩
  rcases he2 γ 𝓖γ with ⟨v2, 𝓥v2, ev2⟩
  refine ⟨ .pair v1 v2 , ?_, ?_ ⟩
  simp [ValOf, 𝓥v1, 𝓥v2]
  simp [Eval.pair, ev1, ev2]

theorem fst {Γ e A B} :
  Γ ⊨ e ∶ .prod A B ->
  Γ ⊨ .fst e ∶ A := by
  intro he
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he γ 𝓖γ with ⟨v, 𝓥v, ev⟩
  rcases v <;> simp [ValOf] at 𝓥v
  rename_i v1 v2
  rcases 𝓥v with ⟨ 𝓥v1, 𝓥v2 ⟩
  refine ⟨ v1 , ?_, ?_ ⟩
  simp [𝓥v1]
  apply Eval.fst ev

theorem snd {Γ e A B} :
  Γ ⊨ e ∶ .prod A B ->
  Γ ⊨ .snd e ∶ B := by
  intro he
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he γ 𝓖γ with ⟨v, 𝓥v, ev⟩
  rcases v <;> simp [ValOf] at 𝓥v
  rename_i v1 v2
  rcases 𝓥v with ⟨ 𝓥v1, 𝓥v2 ⟩
  refine ⟨ v2 , ?_, ?_ ⟩
  simp [𝓥v2]
  apply Eval.snd ev

theorem inl {Γ e A B} :
  Γ ⊨ e ∶ A ->
  Γ ⊨ .inl e ∶ .sum A B := by
  intro he
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he γ 𝓖γ with ⟨v, 𝓥v, ev⟩
  refine ⟨ .inl v , ?_, ?_ ⟩
  simp [ValOf, 𝓥v]
  simp [Eval.inl, ev]

theorem inr {Γ e A B} :
  Γ ⊨ e ∶ B ->
  Γ ⊨ .inr e ∶ .sum A B := by
  intro he
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he γ 𝓖γ with ⟨v, 𝓥v, ev⟩
  refine ⟨ .inr v , ?_, ?_ ⟩
  simp [ValOf, 𝓥v]
  simp [Eval.inr, ev]

theorem case {Γ e0 e1 e2 A B C} :
  Γ ⊨ e0 ∶ .sum A B ->
  Γ ; A ⊨ e1 ∶ C ->
  Γ ; B ⊨ e2 ∶ C ->
  Γ ⊨ .case e0 e1 e2 ∶ C := by
  intro he0 he1 he2
  simp [SemTyp] at *
  intros γ 𝓖γ
  unfold ExpOf at *
  rcases he0 γ 𝓖γ with ⟨v0, 𝓥v0, ev0⟩
  rcases v0 <;> simp [ValOf] at 𝓥v0
  case inl =>
    rename_i v0
    rcases he1 (γ ∷ v0) (EnvOf.cons 𝓖γ 𝓥v0) with ⟨v1, 𝓥v1, ev1⟩

    refine ⟨ v1 , 𝓥v1, ?_ ⟩
    apply Eval.case_inl ev0 ev1
  case inr =>
    rename_i v0
    rcases he2 (γ ∷ v0) (EnvOf.cons 𝓖γ 𝓥v0) with ⟨v2, 𝓥v2, ev2⟩

    refine ⟨ v2 , 𝓥v2, ?_ ⟩
    apply Eval.case_inr ev0 ev2

end SemTyp

namespace SemCtx

theorem nil :
  ⊨ [] ∶ ⬝
  := EnvOf.nil

theorem cons {Γ γ v A} :
  ⊨ γ ∶ Γ ->
  ⬝ ⊨ v ∶ A ->
  v.isVal ->
  ⊨ γ ∷ v ∶ Γ ; A
  := fun 𝓖γ hv isv => by
  rcases adequacy hv nil with ⟨v', 𝓥v', ev⟩
  have hv' : v = v' := ev.of_isVal isv
  simp [EnvOf] at *
  refine ⟨ 𝓖γ , ?_ ⟩
  simpa [hv'] using 𝓥v'

end SemCtx

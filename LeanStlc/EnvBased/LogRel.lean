import LeanStlc.EnvBased.Syntax
import LeanStlc.EnvBased.DynSem
import LeanStlc.EnvBased.SynTyp

section
set_option hygiene false
notation:40 "𝓥⟦" A:41 "⟧" "∋" v:40 => ValOf A v
notation:40 "𝓖⟦" Γ:41 "⟧" "∋" γ:40 => EnvOf Γ γ
notation:40 γ:41 "⊩" "𝓔⟦" A:41 "⟧" "∋" e:70 => ExpOf γ A e
notation:40 "⊨"  γ:41 "∶" Γ:41 => EnvOf Γ γ
notation:40 Γ:41 "⊨"  e:41 "∶" A:41 => SemTyp Γ e A
end section

mutual -- ValOf, EnvOf, ExpOf
def ValOf (A:Typ) (v:Exp) : Prop :=
  match A, v with
  | .int, .int _ => True
  | .ctx Ξ, .env ξ => 𝓖⟦ Ξ ⟧ ∋ ξ
  | .unit, .unit => True
  | .prod A  B, .pair v1 v2 => 𝓥⟦ A ⟧ ∋ v1 ∧ 𝓥⟦ B ⟧ ∋ v2
  | .sum  A _B, .inl v => 𝓥⟦ A ⟧ ∋ v
  | .sum _A  B, .inr v => 𝓥⟦ B ⟧ ∋ v
  | .arr  A  B, .clos (.env ξ) e =>
    -- ∃ Ξ, 𝓖⟦ Ξ ⟧ ∋ ξ ∧
    -- -- above is not needed as specified in
    -- -- [A Case for First-Class Environments](https://doi.org/10.1145/3689800)
    ∀ v, 𝓥⟦ A ⟧ ∋ v -> ξ∷v ⊩ 𝓔⟦ B ⟧ ∋ e
  | _, _ => False

def EnvOf : Ctx -> Env -> Prop
  | ⬝, [] => True
  | Γ ; A, γ ∷ v => 𝓖⟦ Γ ⟧ ∋ γ ∧ 𝓥⟦ A ⟧ ∋ v
  | _, _ => False

def ExpOf (γ:Env) (A:Typ) (e:Exp) : Prop :=
  ∃ v, 𝓥⟦ A ⟧ ∋ v ∧ γ ⊩ e ⇓ v
end

def SemTyp (Γ:Ctx) (e:Exp) (A:Typ) : Prop :=
  ∀ γ, 𝓖⟦ Γ ⟧ ∋ γ -> γ ⊩ 𝓔⟦ A ⟧ ∋ e

theorem adequacy {Γ e A} {γ} :
  Γ ⊨ e ∶ A ->
  𝓖⟦ Γ ⟧ ∋ γ ->
  ∃ v,
    𝓥⟦ A ⟧ ∋ v
  ∧ γ ⊩ e ⇓ v :=
  fun wt 𝓖γ => by
  unfold SemTyp ExpOf at wt
  apply wt _ 𝓖γ

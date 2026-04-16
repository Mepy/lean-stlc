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
    -- -- we instead strengthen that ξ isVal syntactically
    ξ.isVal ∧
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

mutual -- ValOf.isVal, EnvOf.isVal
theorem ValOf.isVal {A v} :
  𝓥⟦ A ⟧ ∋ v ->
  v.isVal :=
  fun 𝓥v => by
  cases A <;> cases v <;> try simp [ValOf] at 𝓥v
  case int.int => constructor
  case unit.unit => constructor
  case prod.pair =>
    rename_i v1 v2
    rcases 𝓥v with ⟨𝓥v1, 𝓥v2⟩
    have isv1 : v1.isVal := ValOf.isVal 𝓥v1
    have isv2 : v2.isVal := ValOf.isVal 𝓥v2
    apply Exp.isVal.pair isv1 isv2
  case ctx.env =>
    rename_i ξ
    have isξ : ξ.isVal := EnvOf.isVal 𝓥v
    apply Exp.isVal.env isξ
  case sum.inl =>
    rename_i v
    have isv : v.isVal := ValOf.isVal 𝓥v
    apply Exp.isVal.inl isv
  case sum.inr =>
    rename_i v
    have isv : v.isVal := ValOf.isVal 𝓥v
    apply Exp.isVal.inr isv
  case arr.clos =>
    rename_i ξ e
    rcases ξ <;> simp [ValOf] at 𝓥v
    rcases 𝓥v with ⟨isξ, _⟩
    apply Exp.isVal.clos (Exp.isVal.env isξ)
theorem EnvOf.isVal {Γ γ} :
  𝓖⟦ Γ ⟧ ∋ γ ->
  γ.isVal :=
  fun 𝓖γ => by
  cases Γ <;> cases γ <;> try simp [EnvOf] at 𝓖γ
  case nil.nil => constructor
  case cons.cons =>
    rename_i γ v
    rcases 𝓖γ with ⟨𝓖γ, 𝓥v⟩
    have isγ : γ.isVal := EnvOf.isVal 𝓖γ
    have isv : v.isVal := ValOf.isVal 𝓥v
    apply Env.isVal.cons isγ isv
end

theorem adequacy {Γ e A} {γ} :
  Γ ⊨ e ∶ A ->
  𝓖⟦ Γ ⟧ ∋ γ ->
  ∃ v,
    v.isVal
  ∧ 𝓥⟦ A ⟧ ∋ v
  ∧ γ ⊩ e ⇓ v :=
  fun wt 𝓖γ => by
  unfold SemTyp ExpOf at wt
  rcases wt γ 𝓖γ with ⟨ v, 𝓥v, ev ⟩
  have isv := ValOf.isVal 𝓥v
  refine ⟨ v, isv, 𝓥v, ev ⟩

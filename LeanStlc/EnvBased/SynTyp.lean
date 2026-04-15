import LeanStlc.EnvBased.Syntax
mutual -- Typ, Ctx
inductive Typ : Type where
  | int
  | ctx (Γ : Ctx)
  | unit
  | prod (A1 A2 : Typ)
  | sum (A1 A2 : Typ)
  | arr (A B : Typ)
deriving Repr
inductive Ctx : Type where
  | nil
  | cons (Γ : Ctx) (A : Typ)
deriving Repr
end

notation:50 "⬝" => Ctx.nil
infixl:50 ";" => Ctx.cons

section
set_option hygiene false
notation:40 Γ:41 "∋" x:41 "∶" A:41 => Ctx.Has Γ x A
notation:40 "⊢" ξ:41 "∶" Ξ:41 => SynCtx ξ Ξ
notation:40 Γ:41 "⊢" e:41 "∶" A:41 => SynTyp Γ e A
end section

inductive Ctx.Has : Ctx -> Nat -> Typ -> Prop where
  | here {Γ A} : (Γ ; A) ∋ 0 ∶ A
  | there {Γ A A' x} :
    Γ ∋ x ∶ A ->
    Γ ; A' ∋ x + 1 ∶ A


mutual -- SynTyp, SynCtx

inductive SynTyp : Ctx -> Exp -> Typ -> Prop where
  | int {Γ n} :
    ----------------------
    Γ ⊢ .int n ∶ .int
  | env {Γ ξ Ξ} :
    ⊢ ξ ∶ Ξ ->
    ----------------------
    Γ ⊢ .env ξ ∶ .ctx Ξ
  | cur {Γ} :
    ----------------------
    Γ ⊢ .cur ∶ .ctx Γ
  | get {Γ Ξ eξ x A} :
    Γ ⊢ eξ ∶ .ctx Ξ ->
    Ξ ∋ x ∶ A ->
    ----------------------
    Γ ⊢ .get eξ x ∶ A
  | clos {Γ Ξ eξ e A B} :
    Γ ⊢ eξ ∶ .ctx Ξ ->
    Ξ ; A ⊢ e ∶ B ->
    ----------------------
    Γ ⊢ .clos eξ e ∶ .arr A B
  | app {Γ e1 e2 A B} :
    Γ ⊢ e1 ∶ .arr A B ->
    Γ ⊢ e2 ∶ A ->
    ----------------------
    Γ ⊢ .app e1 e2 ∶ B
  | letin {Γ e1 e2 A B} :
    Γ ⊢ e1 ∶ A ->
    Γ ; A ⊢ e2 ∶ B ->
    ----------------------
    Γ ⊢ .letin e1 e2 ∶ B
  | unit {Γ} :
    ----------------------
    Γ ⊢ .unit ∶ .unit
  | pair {Γ e1 e2 A B} :
    Γ ⊢ e1 ∶ A ->
    Γ ⊢ e2 ∶ B ->
    ----------------------
    Γ ⊢ .pair e1 e2 ∶ .prod A B
  | fst {Γ e A B} :
    Γ ⊢ e ∶ .prod A B ->
    ----------------------
    Γ ⊢ .fst e ∶ A
  | snd {Γ e A B} :
    Γ ⊢ e ∶ .prod A B ->
    ----------------------
    Γ ⊢ .snd e ∶ B
  | inl {Γ e A B} :
    Γ ⊢ e ∶ A ->
    ----------------------
    Γ ⊢ .inl e ∶ .sum A B
  | inr {Γ e A B} :
    Γ ⊢ e ∶ B ->
    ----------------------
    Γ ⊢ .inr e ∶ .sum A B
  | case {Γ e0 e1 e2 A B C} :
    Γ ⊢ e0 ∶ .sum A B ->
    Γ ; A ⊢ e1 ∶ C ->
    Γ ; B ⊢ e2 ∶ C ->
    ----------------------
    Γ ⊢ .case e0 e1 e2 ∶ C
inductive SynCtx : Env -> Ctx -> Prop where
  | nil :
    ----------------------
    ⊢ [] ∶ ⬝
  | cons {Γ γ v A} :
    ⊢ γ ∶ Γ ->
    ⬝ ⊢ v ∶ A ->
    v.isVal ->
    ----------------------
    ⊢ γ ∷ v ∶ Γ ; A
end

theorem SynTyp.lam {Γ e A B} :
  Γ ; A ⊢ e ∶ B ->
  -----------------------
  Γ ⊢ .lam e ∶ .arr A B
  := fun H => SynTyp.clos SynTyp.cur H

theorem SynTyp.var {Γ x A} :
  Γ ∋ x ∶ A ->
  -----------------------
  Γ ⊢ .var x ∶ A
  := fun H => SynTyp.get SynTyp.cur H

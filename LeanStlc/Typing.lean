import LeanStlc.Syntax
open Nat

inductive Typ : Type where
  | arr : Typ -> Typ -> Typ
  | unit : Typ
  | prod : Typ -> Typ -> Typ
  | sum : Typ -> Typ -> Typ
deriving Repr

inductive Ctx : Type where
  | nil : Ctx
  | cons : Ctx -> Typ -> Ctx
deriving Repr
notation:50 "⬝" => Ctx.nil
infixl:50 "∷" => Ctx.cons

inductive Ctx.In : Nat -> Typ -> Ctx -> Prop where
  | here {Γ A} : Ctx.In 0 A (Γ ∷ A)
  | there {Γ A B n} : Ctx.In n A Γ -> Ctx.In (n + 1) A (Γ ∷ B)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => Ctx.In x A Γ

section
set_option hygiene false
local notation:40 Γ:41 "⊢" e:41 "∶" A:41 => TypedExp Γ e A
inductive TypedExp : Ctx -> Exp -> Typ -> Prop where
  | var {Γ x A} :
    Γ ∋ x ∶ A ->
    ----------------------
    Γ ⊢ .var x ∶ A
  | lam {Γ A B e} :
    Γ ∷ A ⊢ e ∶ B ->
    ----------------------
    Γ ⊢ .lam e ∶ .arr A B
  | app {Γ e1 e2 A B} :
    Γ ⊢ e1 ∶ .arr A B ->
    Γ ⊢ e2 ∶ A ->
    ----------------------
    Γ ⊢ .app e1 e2 ∶ B
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
    Γ ∷ A ⊢ e1 ∶ C ->
    Γ ∷ B ⊢ e2 ∶ C ->
    ----------------------
    Γ ⊢ .case e0 e1 e2 ∶ C
end
notation:40 Γ:41 "⊢" e:41 "∶" A:41 => TypedExp Γ e A

abbrev TypedRenaming (ξ : Renaming) (Γ Δ : Ctx) : Prop :=
  ∀ n A, Γ ∋ n ∶ A -> Δ ∋ ξ n ∶ A
notation:40 Δ:41 "⊢" ξ:41 "∶" Γ:41 => TypedRenaming ξ Γ Δ

theorem TypedSucc {Γ A} : Γ ∷ A ⊢ succ ∶ Γ
  := by intros n B p; constructor; assumption

theorem TypedLift {Γ Δ A} (ξ : Renaming) : (Δ ⊢ ξ ∶ Γ) -> Δ ∷ A ⊢ (lift ξ) ∶ Γ ∷ A
  := fun h n B p => match p with
  | .here => .here
  | .there p' => by
    apply Ctx.In.there
    apply h
    exact p'

theorem TypedRename {ξ} {Γ Δ : Ctx} (hξ : Δ ⊢ ξ ∶ Γ) : ∀ e (A:Typ), (Γ ⊢ e ∶ A) -> Δ ⊢ rename ξ e ∶ A
  :=
  by
  intros e A he;
  induction he
    generalizing ξ Δ
  all_goals constructor
  all_goals apply_rules -- using induction hypothesis
  all_goals apply TypedLift; assumption


theorem TypedRenameSucc {Γ : Ctx} {A B} {e : Exp} : Γ ⊢ e ∶ A -> Γ ∷ B ⊢ rename succ e ∶ A
  := by apply TypedRename; apply TypedSucc

abbrev TypedWeaken := @TypedRenameSucc

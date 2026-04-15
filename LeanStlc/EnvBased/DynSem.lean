import LeanStlc.EnvBased.Syntax

section
set_option hygiene false
notation:40 γ:41 "∋" x:41 "⇒" v:41 => Env.Has γ x v
notation:40 γ:41 "⊩" e:41 "⇓" v:41 => Eval γ e v
end section

inductive Env.Has : Env -> Nat -> Exp -> Prop where
  | here {γ v} : γ ∷ v ∋ 0 ⇒ v
  | there {γ v v' x} :
    γ ∋ x ⇒ v ->
    γ ∷ v' ∋ x + 1 ⇒ v

inductive Eval : Env -> Exp -> Exp -> Prop where
  | int {γ n} :
    ----------------------
    γ ⊩ .int n ⇓ .int n
  | env {γ ξ} :
    ----------------------
    γ ⊩ .env ξ ⇓ .env ξ
  | cur {γ} :
    ----------------------
    γ ⊩ .cur ⇓ .env γ
  | get {γ ξ eξ x v} :
    γ ⊩ eξ ⇓ .env ξ ->
    ξ ∋ x ⇒ v ->
    ----------------------
    γ ⊩ .get eξ x ⇓ v
  | clos {γ ξ eξ e} :
    γ ⊩ eξ ⇓ .env ξ ->
    ----------------------
    γ ⊩ .clos eξ e ⇓ .clos (.env ξ) e
  | app {γ ξ e1 e2 e v2 v} :
    γ ⊩ e1 ⇓ .clos (.env ξ) e ->
    γ ⊩ e2 ⇓ v2 ->
    ξ ∷ v2 ⊩ e ⇓ v ->
    ----------------------
    γ ⊩ .app e1 e2 ⇓ v
  | letin {γ e1 e2 v1 v} :
    γ ⊩ e1 ⇓ v1 ->
    γ ∷ v1 ⊩ e2 ⇓ v ->
    ----------------------
    γ ⊩ .letin e1 e2 ⇓ v
  | unit {γ} :
    ----------------------
    γ ⊩ .unit ⇓ .unit
  | pair {γ e1 e2 v1 v2} :
    γ ⊩ e1 ⇓ v1 ->
    γ ⊩ e2 ⇓ v2 ->
    ----------------------
    γ ⊩ .pair e1 e2 ⇓ .pair v1 v2
  | fst {γ e v1 v2} :
    γ ⊩ e ⇓ .pair v1 v2 ->
    ----------------------
    γ ⊩ .fst e ⇓ v1
  | snd {γ e v1 v2} :
    γ ⊩ e ⇓ .pair v1 v2 ->
    ----------------------
    γ ⊩ .snd e ⇓ v2
  | inl {γ e v} :
    γ ⊩ e ⇓ v ->
    ----------------------
    γ ⊩ .inl e ⇓ .inl v
  | inr {γ e v} :
    γ ⊩ e ⇓ v ->
    ----------------------
    γ ⊩ .inr e ⇓ .inr v
  | case_inl {γ e0 e1 e2 v0 v} :
    γ ⊩ e0 ⇓ .inl v0 ->
    γ ∷ v0 ⊩ e1 ⇓ v ->
    ----------------------
    γ ⊩ .case e0 e1 e2 ⇓ v
  | case_inr {γ e0 e1 e2 v0 v} :
    γ ⊩ e0 ⇓ .inr v0 ->
    γ ∷ v0 ⊩ e2 ⇓ v ->
    ----------------------
    γ ⊩ .case e0 e1 e2 ⇓ v

theorem Env.Has.det :
  γ ∋ x ⇒ v1 ->
  γ ∋ x ⇒ v2 ->
  v1 = v2
  | .here, .here => rfl
  | .there h1, .there h2 => Env.Has.det h1 h2

theorem Eval.det :
  γ ⊩ e ⇓ v1 ->
  γ ⊩ e ⇓ v2 ->
  v1 = v2
  | .int, .int => rfl
  | .env, .env => rfl
  | .cur, .cur => rfl
  | .get heξ hx, .get heξ' hx' =>
    match Eval.det heξ heξ' with
    | rfl => Env.Has.det hx hx'
  | .clos heξ, .clos heξ' =>
    match Eval.det heξ heξ' with
    | rfl => rfl
  | .app he1 he2 he, .app he1' he2' he' =>
    match Eval.det he1 he1', Eval.det he2 he2' with
    | rfl, rfl => Eval.det he he'
  | .letin he1 he2, .letin he1' he2' =>
    match Eval.det he1 he1' with
    | rfl => Eval.det he2 he2'
  | .unit, .unit => rfl
  | .pair he1 he2, .pair he1' he2' =>
    match Eval.det he1 he1', Eval.det he2 he2' with
    | rfl, rfl => rfl
  | .fst he, .fst he' =>
    match Eval.det he he' with
    | rfl => rfl
  | .snd he, .snd he' =>
    match Eval.det he he' with
    | rfl => rfl
  | .inl he, .inl he' =>
    match Eval.det he he' with
    | rfl => rfl
  | .inr he, .inr he' =>
    match Eval.det he he' with
    | rfl => rfl
  | .case_inl he0 he1, .case_inl he0' he1' =>
    match Eval.det he0 he0' with
    | rfl => Eval.det he1 he1'
  | .case_inr he0 he2, .case_inr he0' he2' =>
    match Eval.det he0 he0' with
    | rfl => Eval.det he2 he2'
  | .case_inl he0 _, .case_inr he0' _ =>
    nomatch Eval.det he0 he0' -- kinda exfalso
  | .case_inr he0 _, .case_inl he0' _ =>
    nomatch Eval.det he0 he0' -- kinda exfalso

theorem Eval.of_isVal :
  γ ⊩ e ⇓ v ->
  e.isVal ->
  e = v
  | .int, .int => rfl
  | .env, .env _ => rfl
  | .clos heξ, .clos hξ =>
    match Eval.of_isVal heξ hξ with
    | rfl => rfl
  | .unit, .unit => rfl
  | .pair he1 he2, .pair h1 h2 =>
    match Eval.of_isVal he1 h1, Eval.of_isVal he2 h2 with
    | rfl, rfl => rfl
  | .inl he, .inl h =>
    match Eval.of_isVal he h with
    | rfl => rfl
  | .inr he, .inr h =>
    match Eval.of_isVal he h with
    | rfl => rfl

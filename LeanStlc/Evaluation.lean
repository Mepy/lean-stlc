import LeanStlc.Syntax
import LeanStlc.Reachable

open Nat

section
set_option hygiene false
local infix:40 "⟶" => Eval
inductive Eval : Exp -> Exp -> Prop where
  -- β-reduction rules
  | appLam {e1 e2} :
    .app (.lam e1) e2 ⟶ e1 ⦃ ⟨e2⟩  ⦄

  | fstPair {e1 e2} :
    .fst (.pair e1 e2) ⟶ e1
  | sndPair {e1 e2} :
    .snd (.pair e1 e2) ⟶ e2

  | caseInl {e0 e1 e2} :
    .case (.inl e0) e1 e2 ⟶ e1 ⦃ ⟨e0⟩ ⦄
  | caseInr {e0 e1 e2} :
    .case (.inr e0) e1 e2 ⟶ e2 ⦃ ⟨e0⟩ ⦄

  -- congruence rules
  | app1 {e1 e1' e2} :
    e1 ⟶ e1' ->
    -----------------------------------
    .app e1 e2 ⟶ .app e1' e2
  | app2 {e1 e2 e2'} :
    e2 ⟶ e2' ->
    -----------------------------------
    .app e1 e2 ⟶ .app e1 e2'
  | pair1 {e1 e1' e2} :
    e1 ⟶ e1' ->
    -----------------------------------
    .pair e1 e2 ⟶ .pair e1' e2
  | pair2 {e1 e2 e2'} :
    e2 ⟶ e2' ->
    -----------------------------------
    .pair e1 e2 ⟶ .pair e1 e2'
  | fst {e e'} :
    e ⟶ e' ->
    -----------------------------------
    .fst e ⟶ .fst e'
  | snd {e e'} :
    e ⟶ e' ->
    -----------------------------------
    .snd e ⟶ .snd e'
  | inl {e e'} :
    e ⟶ e' ->
    -----------------------------------
    .inl e ⟶ .inl e'
  | inr {e e'} :
    e ⟶ e' ->
    -----------------------------------
    .inr e ⟶ .inr e'
  | case0 {e0 e0' e1 e2} :
    e0 ⟶ e0' ->
    -----------------------------------
    .case e0 e1 e2 ⟶ .case e0' e1 e2
end
infix:40 "⟶" => Eval

@[reducible]
def Evals := Reachable Eval
infix:40 "⟶*" => Evals
namespace Evals

@[refl]
def refl {e} : e ⟶* e := .base

-- derived β-reduction rules
def appLam {e1 e2} :
  .app (.lam e1) e2 ⟶* e1 ⦃ ⟨e2⟩  ⦄
  := .inj (Eval.appLam)

def fstPair {e1 e2} :
  .fst (.pair e1 e2) ⟶* e1
  := .inj (Eval.fstPair)

def sndPair {e1 e2} :
  .snd (.pair e1 e2) ⟶* e2
  := .inj (Eval.sndPair)

def caseInl {e0 e1 e2} :
  .case (.inl e0) e1 e2 ⟶* e1 ⦃ ⟨e0⟩ ⦄
  := .inj (Eval.caseInl)

def caseInr {e0 e1 e2} :
  .case (.inr e0) e1 e2 ⟶* e2 ⦃ ⟨e0⟩ ⦄
  := .inj (Eval.caseInr)

-- dervied congruence rules
def app1 {e1 e1' e2} :
  e1 ⟶* e1' ->
  ------------------------------------
  .app e1 e2 ⟶* .app e1' e2
  | .base => .base
  | .step p h =>
    .step (Eval.app1 p) (app1 h)

def app2 {e1 e2 e2'} :
  e2 ⟶* e2' ->
  ------------------------------------
  .app e1 e2 ⟶* .app e1 e2'
  | .base => .base
  | .step p h =>
    .step (Eval.app2 p) (app2 h)

def pair1 {e1 e1' e2} :
  e1 ⟶* e1' ->
  ------------------------------------
  .pair e1 e2 ⟶* .pair e1' e2
  | .base => .base
  | .step p h =>
    .step (Eval.pair1 p) (pair1 h)

def pair2 {e1 e2 e2'} :
  e2 ⟶* e2' ->
  ------------------------------------
  .pair e1 e2 ⟶* .pair e1 e2'
  | .base => .base
  | .step p h =>
    .step (Eval.pair2 p) (pair2 h)


def fst {e e'} :
  e ⟶* e' ->
  ------------------------------------
  .fst e ⟶* .fst e'
  | .base => .base
  | .step p h =>
    .step (Eval.fst p) (fst h)

def snd {e e'} :
  e ⟶* e' ->
  ------------------------------------
  .snd e ⟶* .snd e'
  | .base => .base
  | .step p h =>
    .step (Eval.snd p) (snd h)

def inl {e e'} :
  e ⟶* e' ->
  ------------------------------------
  .inl e ⟶* .inl e'
  | .base => .base
  | .step p h =>
    .step (Eval.inl p) (inl h)

def inr {e e'} :
  e ⟶* e' ->
  ------------------------------------
  .inr e ⟶* .inr e'
  | .base => .base
  | .step p h =>
    .step (Eval.inr p) (inr h)

def case0 {e0 e0' e1 e2} :
  e0 ⟶* e0' ->
  ------------------------------------
  .case e0 e1 e2 ⟶* .case e0' e1 e2
  | .base => .base
  | .step p h =>
    .step (Eval.case0 p) (case0 h)

-- big-step rules
def app {e1 e2} {e1'} {e2'} {e'} :
  e1 ⟶* .lam e1' ->
  e2 ⟶* e2' ->
  e1' ⦃ ⟨e2'⟩  ⦄ ⟶* e' ->
  ------------------------------------
  .app e1 e2 ⟶* e'
  := by
    intros h1 h2  h3
    calc
      _ ⟶* .app (.lam e1') e2  := app1 h1
      _ ⟶* .app (.lam e1') e2' := app2 h2
      _ ⟶* e1' ⦃ ⟨e2'⟩ ⦄ := appLam
      _ ⟶* e' := h3


end Evals

mutual -- Exp, Env
inductive Exp : Type where
  | int (n : Int)
  | env (ξ : Env)
  | cur -- env
  | get (e : Exp) (x : Nat)  -- de Bruijn indexed varaibles, we range `x` over dbi
  | clos (eξ : Exp) (/- bind 1 -/ e : Exp)
  | app (e1 e2 : Exp)
  | letin (e1 e2 : Exp)
  | unit
  | pair (e1 e2 : Exp)
  | fst (e : Exp)
  | snd (e : Exp)
  | inl (e : Exp)
  | inr (e : Exp)
  | case (e1 e2 e3 : Exp)
deriving Repr
inductive Env : Type where
  | nil
  | cons (env : Env) (e : Exp)
deriving Repr
end
notation:50 "[]" => Env.nil
infixl:50 "∷" => Env.cons

@[simp] def Exp.lam (e : Exp) : Exp := Exp.clos Exp.cur e
@[simp] def Exp.var (x : Nat) : Exp := Exp.get Exp.cur x

mutual -- Exp.isVal, Env.isVal

inductive Exp.isVal : Exp -> Prop where
  | int {n} : Exp.isVal (.int n)
  | env {ξ} :
    Env.isVal ξ ->
    --------------------
    Exp.isVal (.env ξ)
  | clos {eξ e} :
    Exp.isVal eξ ->
    --------------------
    Exp.isVal (.clos eξ e)
  | unit : Exp.isVal .unit
  | pair {e1 e2} :
    Exp.isVal e1 ->
    Exp.isVal e2 ->
    --------------------
    Exp.isVal (.pair e1 e2)
  | inl {e} :
    Exp.isVal e ->
    --------------------
    Exp.isVal (.inl e)
  | inr {e} :
    Exp.isVal e ->
    --------------------
    Exp.isVal (.inr e)
inductive Env.isVal : Env -> Prop where
  | nil : [].isVal
  | cons {env e} :
    env.isVal ->
    e.isVal ->
    --------------------
    (env ∷ e).isVal
end

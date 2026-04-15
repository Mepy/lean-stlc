import LeanStlc.EnvBased.Syntax
import LeanStlc.EnvBased.DynSem
import LeanStlc.EnvBased.SynTyp
import LeanStlc.EnvBased.LogRel
import LeanStlc.EnvBased.SemTyp

mutual -- SynTyp.fundamental, SynCtx.fundamental
theorem SynTyp.fundamental {Γ e A} :
  Γ ⊢ e ∶ A ->
  Γ ⊨ e ∶ A
  | .int =>
      SemTyp.int
  | .env hξ =>
      SemTyp.env hξ.fundamental
  | .cur =>
      SemTyp.cur
  | .get heξ hx =>
      SemTyp.get heξ.fundamental hx
  | .clos heξ he =>
      SemTyp.clos heξ.fundamental he.fundamental
  | .app he1 he2 =>
      SemTyp.app he1.fundamental he2.fundamental
  | .letin he1 he2 =>
      SemTyp.letin he1.fundamental he2.fundamental
  | .unit =>
      SemTyp.unit
  | .pair he1 he2 =>
      SemTyp.pair he1.fundamental he2.fundamental
  | .fst he =>
      SemTyp.fst he.fundamental
  | .snd he =>
      SemTyp.snd he.fundamental
  | .inl he =>
      SemTyp.inl he.fundamental
  | .inr he =>
      SemTyp.inr he.fundamental
  | .case he0 he1 he2 =>
      SemTyp.case he0.fundamental he1.fundamental he2.fundamental

theorem SynCtx.fundamental {γ Γ} :
  ⊢ γ ∶ Γ ->
  ⊨ γ ∶ Γ
  | .nil => SemCtx.nil
  | .cons hγ' he isv =>
    SemCtx.cons hγ'.fundamental he.fundamental isv

end

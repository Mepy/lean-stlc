inductive Reachable {A : Type} (R : A -> A -> Prop) : A -> A -> Prop where
  | base {x} : Reachable R x x
  | step {x y z} : R x y -> Reachable R y z -> Reachable R x z

namespace Reachable

@[refl] def rfl {x} := @Reachable.base x

def refl {A} {R} (x : A) : Reachable R x x := .base

def trans {A} {R} {x y z : A} (h1 : Reachable R x y) (h2 : Reachable R y z) : Reachable R x z
  := match h1 with
  | .base => h2
  | .step p h1 =>
    .step p (trans h1 h2)

def inj {A R} {x y : A} (h : R x y) : Reachable R x y := .step h .base

instance {A} {R : A -> A -> Prop} : Trans R (Reachable R) (Reachable R) where
  trans := step

instance {A} {R : A -> A -> Prop} : Trans (Reachable R) (Reachable R) (Reachable R) where
  trans := trans

instance {A} {R : A -> A -> Prop} : Trans R R (Reachable R) where
  trans p1 p2 := .step p1 (inj p2)

instance {A} {R : A -> A -> Prop} : Trans (Reachable R) R (Reachable R) where
  trans p1 p2 := trans p1 (inj p2)

end Reachable

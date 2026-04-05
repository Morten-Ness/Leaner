import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_sub_le {f g : R'[A]} :
    (f - g).supDegree D ≤ f.supDegree D ⊔ g.supDegree D := by
  rw [sub_eq_add_neg, ← AddMonoidAlgebra.supDegree_neg (f := g)]; apply AddMonoidAlgebra.supDegree_add_le


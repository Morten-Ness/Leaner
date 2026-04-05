import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

set_option backward.isDefEq.respectTransparency false in
theorem supDegree_neg {f : R'[A]} :
    (-f).supDegree D = f.supDegree D := by
  rw [supDegree, supDegree, Finsupp.support_neg]


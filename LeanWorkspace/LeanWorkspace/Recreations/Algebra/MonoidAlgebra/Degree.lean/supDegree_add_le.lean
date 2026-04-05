import Mathlib

variable {R R' A T B ι : Type*}

variable [Semiring R] [Ring R']

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

theorem supDegree_add_le {f g : R[A]} :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) := AddMonoidAlgebra.sup_support_add_le D f g


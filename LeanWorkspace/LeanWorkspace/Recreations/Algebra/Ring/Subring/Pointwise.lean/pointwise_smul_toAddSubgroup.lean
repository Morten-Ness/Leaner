import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem pointwise_smul_toAddSubgroup (m : M) (S : Subring R) :
    (m • S).toAddSubgroup = m • S.toAddSubgroup := rfl


import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem pointwise_smul_toSubsemiring (m : M) (S : Subring R) :
    (m • S).toSubsemiring = m • S.toSubsemiring := rfl


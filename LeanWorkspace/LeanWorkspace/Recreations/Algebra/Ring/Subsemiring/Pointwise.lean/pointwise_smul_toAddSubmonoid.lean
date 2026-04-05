import Mathlib

variable {M R : Type*}

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

theorem pointwise_smul_toAddSubmonoid (m : M) (S : Subsemiring R) :
    (m • S).toAddSubmonoid = m • S.toAddSubmonoid := rfl


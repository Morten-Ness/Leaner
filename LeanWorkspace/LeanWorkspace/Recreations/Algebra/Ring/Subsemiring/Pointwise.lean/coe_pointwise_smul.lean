import Mathlib

variable {M R : Type*}

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : ↑(m • S) = m • (S : Set R) := rfl


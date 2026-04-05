import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem coe_pointwise_smul (m : M) (S : Subring R) : ↑(m • S) = m • (S : Set R) := rfl


import Mathlib

variable {M R : Type*}

variable [Monoid M] [Semiring R] [MulSemiringAction M R]

theorem pointwise_smul_def {a : M} (S : Subsemiring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) := rfl


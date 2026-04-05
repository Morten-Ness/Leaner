import Mathlib

variable {M R : Type*}

variable [Monoid M] [Ring R] [MulSemiringAction M R]

theorem pointwise_smul_def {a : M} (S : Subring R) :
    a • S = S.map (MulSemiringAction.toRingHom _ _ a) := rfl


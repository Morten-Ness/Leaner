import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem opLinearEquiv_symm_toAddEquiv :
    (MulOpposite.opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm := rfl


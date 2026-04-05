import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem opLinearEquiv_toAddEquiv : (MulOpposite.opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv := rfl


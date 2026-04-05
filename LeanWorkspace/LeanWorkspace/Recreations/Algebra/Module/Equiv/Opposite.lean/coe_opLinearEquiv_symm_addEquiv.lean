import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv_symm_addEquiv :
    ((MulOpposite.opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm : Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm := rfl


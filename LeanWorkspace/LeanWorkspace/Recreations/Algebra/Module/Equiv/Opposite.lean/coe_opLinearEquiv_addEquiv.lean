import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv_addEquiv : ((MulOpposite.opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv := rfl


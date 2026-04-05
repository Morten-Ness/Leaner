import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv_toLinearMap : ((MulOpposite.opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op := rfl


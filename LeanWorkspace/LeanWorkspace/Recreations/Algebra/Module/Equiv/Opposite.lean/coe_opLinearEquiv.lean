import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv : (MulOpposite.opLinearEquiv R : M → Mᵐᵒᵖ) = op := rfl


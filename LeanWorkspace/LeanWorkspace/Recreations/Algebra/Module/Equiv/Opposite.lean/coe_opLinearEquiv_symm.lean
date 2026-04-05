import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv_symm : ((MulOpposite.opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop := rfl


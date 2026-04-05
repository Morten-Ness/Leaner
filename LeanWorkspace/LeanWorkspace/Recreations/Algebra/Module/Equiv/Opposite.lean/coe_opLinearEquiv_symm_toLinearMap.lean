import Mathlib

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

theorem coe_opLinearEquiv_symm_toLinearMap :
    ((MulOpposite.opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop := rfl


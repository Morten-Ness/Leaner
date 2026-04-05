import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_zero : (0 : tsze R M)⁻¹ = (0 : tsze R M) := by
  rw [← TrivSqZeroExt.inl_zero, TrivSqZeroExt.inv_inl, inv_zero]


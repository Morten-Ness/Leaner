import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_one : (1 : tsze R M)⁻¹ = (1 : tsze R M) := by
  rw [← TrivSqZeroExt.inl_one, TrivSqZeroExt.inv_inl, inv_one]


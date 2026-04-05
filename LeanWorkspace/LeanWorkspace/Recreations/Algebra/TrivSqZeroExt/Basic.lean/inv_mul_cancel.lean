import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_mul_cancel {x : tsze R M} (hx : TrivSqZeroExt.fst x ≠ 0) : x⁻¹ * x = 1 := by
  convert TrivSqZeroExt.mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx) using 2
  ext <;> simp


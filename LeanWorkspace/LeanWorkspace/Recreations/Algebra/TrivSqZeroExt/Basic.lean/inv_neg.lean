import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_neg {x : tsze R M} : (-x)⁻¹ = -(x⁻¹) := by
  ext <;> simp [inv_neg]


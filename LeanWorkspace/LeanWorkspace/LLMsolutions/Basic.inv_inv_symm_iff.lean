FAIL
import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a x y : G}

theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x := by
  change x⁻¹ * a⁻¹ = a⁻¹ * y⁻¹ ↔ a * y = x * a
  rw [← inv_eq_iff_eq_inv]
  simpa [mul_inv_rev] using Iff.rfl

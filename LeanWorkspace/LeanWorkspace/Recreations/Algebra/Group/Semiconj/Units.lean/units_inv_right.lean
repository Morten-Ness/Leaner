import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ := calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]


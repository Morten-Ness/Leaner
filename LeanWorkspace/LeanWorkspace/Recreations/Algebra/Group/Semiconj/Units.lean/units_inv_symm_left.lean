import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x := calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]


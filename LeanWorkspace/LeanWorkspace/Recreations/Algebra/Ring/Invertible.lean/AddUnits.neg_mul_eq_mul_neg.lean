import Mathlib

open scoped Ring

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R] (x : AddUnits R) (y : R)

theorem AddUnits.neg_mul_eq_mul_neg {x y : AddUnits R} : (↑(-x) * y : R) = x * ↑(-y) := by
  rw [← neg_eq_val_neg, ← val_neg_mulRight]
  apply AddUnits.neg_eq_of_add_eq_zero_left
  simp [← mul_add]


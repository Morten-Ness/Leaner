import Mathlib

variable {R S : Type*}

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

theorem isRegular_iff_eq_zero_of_mul :
    IsRegular r ↔ (∀ x, r * x = 0 → x = 0) ∧ (∀ x, x * r = 0 → x = 0) := by
  rw [isRegular_iff, isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul]


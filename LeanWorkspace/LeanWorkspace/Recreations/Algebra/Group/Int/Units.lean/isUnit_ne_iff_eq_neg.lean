import Mathlib

variable {u v : ℤ}

theorem isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u ≠ v ↔ u = -v := by
  obtain rfl | rfl := Int.isUnit_eq_one_or hu <;> obtain rfl | rfl := Int.isUnit_eq_one_or hv <;> decide


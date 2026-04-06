import Mathlib

variable {u v : ℤ}

theorem isUnit_ne_iff_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u ≠ v ↔ u = -v := by
  rcases hu with ⟨u', rfl⟩
  rcases hv with ⟨v', rfl⟩
  fin_cases u' <;> fin_cases v' <;> norm_num

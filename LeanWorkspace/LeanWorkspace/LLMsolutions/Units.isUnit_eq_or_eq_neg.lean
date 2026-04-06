import Mathlib

variable {u v : ℤ}

theorem isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v := by
  rcases Int.isUnit_iff.mp hu with rfl | rfl
  · rcases Int.isUnit_iff.mp hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rcases Int.isUnit_iff.mp hv with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

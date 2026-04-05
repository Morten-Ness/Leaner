import Mathlib

variable {u v : ℤ}

theorem eq_one_or_neg_one_of_mul_eq_neg_one' (h : u * v = -1) : u = 1 ∧ v = -1 ∨ u = -1 ∧ v = 1 := by
  obtain rfl | rfl := Int.isUnit_eq_one_or (IsUnit.mul_iff.mp (Int.isUnit_iff.mpr (Or.inr h))).1
  · exact Or.inl ⟨rfl, one_mul v ▸ h⟩
  · simpa [Int.neg_mul] using h


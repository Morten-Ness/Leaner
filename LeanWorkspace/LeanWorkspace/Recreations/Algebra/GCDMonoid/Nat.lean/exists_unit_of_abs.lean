import Mathlib

theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (_ : IsUnit u), (Int.natAbs a : ℤ) = u * a := by
  rcases natAbs_eq a with h | h
  · use 1, isUnit_one
    rw [← h, one_mul]
  · use -1, isUnit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]


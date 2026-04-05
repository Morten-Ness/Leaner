import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to ℕ using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
  · simp
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]


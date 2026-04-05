import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_nonpos {a : ℤ} (ha : a ≤ 0) (b : ℕ) : mkRat a b ≤ 0 := by
  obtain rfl | hb := eq_or_ne b 0
  · simp
  · exact (Rat.mkRat_nonpos_iff a hb).mpr ha


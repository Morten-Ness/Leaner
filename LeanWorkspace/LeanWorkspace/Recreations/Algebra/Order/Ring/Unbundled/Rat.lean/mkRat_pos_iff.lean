import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_pos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b ↔ 0 < a := by
  grind [Rat.mkRat_nonneg_iff, Rat.mkRat_eq_zero]


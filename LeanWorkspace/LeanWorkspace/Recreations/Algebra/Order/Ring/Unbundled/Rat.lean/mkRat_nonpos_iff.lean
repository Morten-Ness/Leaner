import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_nonpos_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : mkRat a b ≤ 0 ↔ a ≤ 0 := by
  grind [Rat.mkRat_pos_iff]


import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_nonneg_iff (a : ℤ) {b : ℕ} (hb : b ≠ 0) : 0 ≤ mkRat a b ↔ 0 ≤ a := divInt_nonneg_iff_of_pos_right (show 0 < (b : ℤ) by simpa using Nat.pos_of_ne_zero hb)


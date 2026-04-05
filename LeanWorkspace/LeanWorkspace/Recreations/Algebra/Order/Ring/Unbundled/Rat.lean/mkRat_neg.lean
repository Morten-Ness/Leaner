import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_neg {a : ℤ} (ha : a < 0) {b : ℕ} (hb : b ≠ 0) : mkRat a b < 0 := (Rat.mkRat_neg_iff a hb).mpr ha


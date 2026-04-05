import Mathlib

variable {a b c p q : ℚ}

theorem mkRat_pos {a : ℤ} (ha : 0 < a) {b : ℕ} (hb : b ≠ 0) : 0 < mkRat a b := (Rat.mkRat_pos_iff a hb).mpr ha


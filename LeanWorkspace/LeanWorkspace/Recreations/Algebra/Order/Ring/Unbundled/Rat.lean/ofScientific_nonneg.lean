import Mathlib

variable {a b c p q : ℚ}

theorem ofScientific_nonneg (m : ℕ) (s : Bool) (e : ℕ) : 0 ≤ Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [if_neg (by decide)]
    exact num_nonneg.mp <| Int.natCast_nonneg _
  · grind [normalize_eq_mkRat, Rat.mkRat_nonneg]


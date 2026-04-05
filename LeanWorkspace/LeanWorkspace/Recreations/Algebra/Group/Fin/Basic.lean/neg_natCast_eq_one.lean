import Mathlib

variable {n : ℕ}

theorem neg_natCast_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp only [natCast_eq_last, neg_last]


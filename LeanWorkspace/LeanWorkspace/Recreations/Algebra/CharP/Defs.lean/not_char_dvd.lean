import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]


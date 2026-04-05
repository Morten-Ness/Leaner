import Mathlib

variable {n : ℕ}

theorem lt_sub_iff {n : ℕ} {a b : Fin n} : a < a - b ↔ a < b := by
  fin_omega


import Mathlib

variable {n : ℕ}

theorem rev_add (a b : Fin n) : rev (a + b) = rev a - b := by
  cases n
  · exact a.elim0
  rw [← last_sub, ← last_sub, sub_add_eq_sub_sub]


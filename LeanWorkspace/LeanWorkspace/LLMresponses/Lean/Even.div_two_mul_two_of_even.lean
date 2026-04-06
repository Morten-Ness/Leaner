import Mathlib

variable {m n : ℕ}

theorem div_two_mul_two_of_even : Even n → n / 2 * 2 = n := by
  intro hn
  exact Nat.div_two_mul_two_of_even hn

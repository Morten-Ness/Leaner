import Mathlib

variable {m n : ℕ}

theorem two_mul_div_two_of_even : Even n → 2 * (n / 2) = n := by
  intro hn
  exact Nat.two_mul_div_two_of_even hn

import Mathlib

variable {m n : ℤ}

theorem ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n := by grind

-- Here are examples of how `parity_simps` can be used with `Int`.
example (m n : ℤ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp +decide [*, parity_simps]

example : ¬Even (25394535 : ℤ) := by decide


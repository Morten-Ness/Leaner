import Mathlib

theorem negOnePow_two_mul (n : ℤ) : (2 * n).negOnePow = 1 := Int.negOnePow_even _ ⟨n, two_mul n⟩


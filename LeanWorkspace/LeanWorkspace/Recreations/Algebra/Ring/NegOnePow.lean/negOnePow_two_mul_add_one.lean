import Mathlib

theorem negOnePow_two_mul_add_one (n : ℤ) : (2 * n + 1).negOnePow = -1 := Int.negOnePow_odd _ ⟨n, rfl⟩


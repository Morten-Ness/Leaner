import Mathlib

theorem negOnePow_odd (n : ℤ) (hn : Odd n) : n.negOnePow = -1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_one, mul_neg, mul_one]


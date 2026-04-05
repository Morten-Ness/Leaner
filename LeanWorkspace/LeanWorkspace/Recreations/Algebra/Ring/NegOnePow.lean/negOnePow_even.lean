import Mathlib

theorem negOnePow_even (n : ℤ) (hn : Even n) : n.negOnePow = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [Int.negOnePow_add, units_mul_self]


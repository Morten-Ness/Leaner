import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normUnit_mul_normUnit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using Subsingleton.elim a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [normUnit_zero, zero_mul, normUnit_zero]
  · rw [normUnit_mul h (Units.ne_zero _), normUnit_coe_units, mul_inv_eq_one]


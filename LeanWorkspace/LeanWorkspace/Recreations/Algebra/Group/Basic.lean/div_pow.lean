import Mathlib

variable {α β G M : Type*}

variable [DivisionCommMonoid α] (a b c d : α)

theorem div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  simp only [div_eq_mul_inv, mul_pow, inv_pow]


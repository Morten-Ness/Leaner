import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp only [one_div, inv_pow]


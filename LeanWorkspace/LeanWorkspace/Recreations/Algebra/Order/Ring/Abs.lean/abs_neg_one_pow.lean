import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem abs_neg_one_pow (n : ℕ) : |(-1 : α) ^ n| = 1 := by rw [← pow_abs, abs_neg, abs_one, one_pow]


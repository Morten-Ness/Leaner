import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem pow_abs (a : α) (n : ℕ) : |a| ^ n = |a ^ n| := (abs_pow a n).symm


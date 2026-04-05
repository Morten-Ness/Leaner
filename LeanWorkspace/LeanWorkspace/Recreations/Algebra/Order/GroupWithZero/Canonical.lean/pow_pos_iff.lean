import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

variable [NoZeroDivisors α]

theorem pow_pos_iff (hn : n ≠ 0) : 0 < a ^ n ↔ 0 < a := by simp_rw [zero_lt_iff, pow_ne_zero_iff hn]


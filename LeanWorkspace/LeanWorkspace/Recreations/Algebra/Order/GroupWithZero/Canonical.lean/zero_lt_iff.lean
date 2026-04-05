import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommMonoidWithZero α] {a b : α} {n : ℕ}

theorem zero_lt_iff : 0 < a ↔ a ≠ 0 := by simp [lt_iff_le_and_ne, eq_comm]


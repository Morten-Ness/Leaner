import Mathlib

variable {F α β : Type*}

variable [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : ℕ}

theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by rw [Nat.lt_ceil, cast_zero]


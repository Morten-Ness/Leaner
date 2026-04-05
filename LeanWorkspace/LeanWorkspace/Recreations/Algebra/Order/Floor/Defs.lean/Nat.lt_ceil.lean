import Mathlib

variable {F α β : Type*}

variable [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : ℕ}

theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a := lt_iff_lt_of_le_iff_le Nat.ceil_le


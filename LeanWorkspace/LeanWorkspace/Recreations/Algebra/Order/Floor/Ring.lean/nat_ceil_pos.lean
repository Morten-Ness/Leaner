import Mathlib

variable {α : Type*}

theorem nat_ceil_pos [Semiring α] [LinearOrder α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ := Nat.ceil_pos.2


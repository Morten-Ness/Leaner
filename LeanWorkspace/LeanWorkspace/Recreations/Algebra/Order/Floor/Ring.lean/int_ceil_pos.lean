import Mathlib

variable {α : Type*}

theorem int_ceil_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ := Int.ceil_pos.2


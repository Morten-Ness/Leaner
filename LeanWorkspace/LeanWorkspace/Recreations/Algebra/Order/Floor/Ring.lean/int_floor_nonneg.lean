import Mathlib

variable {α : Type*}

theorem int_floor_nonneg [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ := Int.floor_nonneg.2 ha


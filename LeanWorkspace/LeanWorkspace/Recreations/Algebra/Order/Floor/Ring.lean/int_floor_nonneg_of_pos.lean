import Mathlib

variable {α : Type*}

theorem int_floor_nonneg_of_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ := Mathlib.Meta.Positivity.int_floor_nonneg ha.le


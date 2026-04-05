import Mathlib

variable {α : Type*} {x y : α}

variable [PartialOrder α]

theorem one_le_iff_ne_zero [AddMonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [SuccAddOrder α] [CanonicallyOrderedAdd α] : 1 ≤ x ↔ x ≠ 0 := by
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]


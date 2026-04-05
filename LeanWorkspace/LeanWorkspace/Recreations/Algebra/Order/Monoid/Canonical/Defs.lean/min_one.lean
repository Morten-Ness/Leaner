import Mathlib

variable {α : Type u}

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

theorem min_one (a : α) : min a 1 = 1 := min_eq_right (one_le a)


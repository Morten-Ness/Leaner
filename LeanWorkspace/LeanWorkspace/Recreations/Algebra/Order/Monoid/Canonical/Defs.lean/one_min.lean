import Mathlib

variable {α : Type u}

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

theorem one_min (a : α) : min 1 a = 1 := min_eq_left (one_le a)


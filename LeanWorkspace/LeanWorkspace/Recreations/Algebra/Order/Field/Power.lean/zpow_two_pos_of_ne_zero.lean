import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_two_pos_of_ne_zero (ha : a ≠ 0) : 0 < a ^ (2 : ℤ) := even_two.zpow_pos ha


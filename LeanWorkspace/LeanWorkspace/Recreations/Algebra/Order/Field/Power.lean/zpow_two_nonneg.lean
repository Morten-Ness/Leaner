import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := even_two.zpow_nonneg _


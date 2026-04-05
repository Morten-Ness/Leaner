import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem abs_neg_one_zpow (p : ℤ) : |(-1 : α) ^ p| = 1 := by simp


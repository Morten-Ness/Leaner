import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem abs_zpow (a : α) (p : ℤ) : |a ^ p| = |a| ^ p := map_zpow₀ absHom a p


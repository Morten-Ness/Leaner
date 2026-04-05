import Mathlib

variable {F α β : Type*}

variable [DivisionMonoid α] {a : α}

theorem IsSquare.zpow (n : ℤ) : IsSquare a → IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_zpow)


import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem empty_zpow (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by cases n <;> aesop


import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem empty_zpow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by cases n <;> simp_all


import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem singleton_zpow (a : α) (n : ℤ) : ({a} : Finset α) ^ n = {a ^ n} := by cases n <;> simp


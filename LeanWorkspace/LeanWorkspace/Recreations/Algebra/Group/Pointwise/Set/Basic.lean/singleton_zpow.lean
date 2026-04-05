import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem singleton_zpow (a : α) (n : ℤ) : ({a} : Set α) ^ n = {a ^ n} := by cases n <;> simp


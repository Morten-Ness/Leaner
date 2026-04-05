import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]


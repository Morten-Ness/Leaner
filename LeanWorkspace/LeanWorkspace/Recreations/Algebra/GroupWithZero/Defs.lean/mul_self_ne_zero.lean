import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not


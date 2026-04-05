import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not


import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := (mul_right_injective₀ ha).eq_iff


import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := (mul_left_injective₀ hc).eq_iff


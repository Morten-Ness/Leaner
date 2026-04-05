import Mathlib

variable {M₀ G₀ : Type*}

variable {a b c : M₀}

variable [MulZeroOneClass M₀]

theorem eq_zero_of_mul_eq_self_right [IsLeftCancelMulZero M₀] (h₁ : b ≠ 1) (h₂ : a * b = a) :
    a = 0 := Classical.byContradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm


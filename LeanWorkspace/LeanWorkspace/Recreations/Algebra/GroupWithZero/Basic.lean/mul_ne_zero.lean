import Mathlib

variable {M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩


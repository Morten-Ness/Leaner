import Mathlib

variable {M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 := (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id


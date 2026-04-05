import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroClass M₀] {a b : M₀}

theorem zero_mul_eq_const : ((0 : M₀) * ·) = Function.const _ 0 := funext zero_mul


import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 := mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm


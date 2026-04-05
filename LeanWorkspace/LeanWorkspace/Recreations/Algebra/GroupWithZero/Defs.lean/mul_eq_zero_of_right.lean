import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a


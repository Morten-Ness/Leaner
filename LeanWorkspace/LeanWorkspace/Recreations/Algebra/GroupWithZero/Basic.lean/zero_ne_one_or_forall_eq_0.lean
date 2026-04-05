import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 := not_or_of_imp eq_zero_of_zero_eq_one


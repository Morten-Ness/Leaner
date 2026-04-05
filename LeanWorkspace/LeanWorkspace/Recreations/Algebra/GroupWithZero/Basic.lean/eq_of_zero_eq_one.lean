import Mathlib

variable {M₀ G₀ : Type*}

variable [MulZeroOneClass M₀]

theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b := @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b


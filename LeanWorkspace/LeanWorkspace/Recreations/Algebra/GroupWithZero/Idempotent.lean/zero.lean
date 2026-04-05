import Mathlib

variable {M₀ : Type*}

variable [MulZeroClass M₀]

theorem zero : IsIdempotentElem (0 : M₀) := mul_zero _


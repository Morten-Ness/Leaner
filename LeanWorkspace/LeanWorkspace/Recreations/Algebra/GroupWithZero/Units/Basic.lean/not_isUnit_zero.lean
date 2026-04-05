import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) := mt isUnit_zero_iff.1 zero_ne_one


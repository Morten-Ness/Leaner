import Mathlib

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

theorem MonoidWithZero.inverse_apply {M : Type*} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = a⁻¹ʳ := rfl


import Mathlib

open scoped Ring

variable {M M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

theorem MonoidWithZero.coe_inverse {M : Type*} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse := rfl


import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := Ring.mul_inverse_rev' (Commute.all _ _)


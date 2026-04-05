import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem mul_eq_add (ψ χ : AddChar A M) : ψ * χ = ψ + χ := rfl


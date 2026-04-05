import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem pow_eq_nsmul (ψ : AddChar A M) (n : ℕ) : ψ ^ n = n • ψ := rfl


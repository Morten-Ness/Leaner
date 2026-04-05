import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem powersMulHom_symm_apply (f : Multiplicative ℕ →* M) : (powersMulHom M).symm f = f (ofAdd 1) := rfl


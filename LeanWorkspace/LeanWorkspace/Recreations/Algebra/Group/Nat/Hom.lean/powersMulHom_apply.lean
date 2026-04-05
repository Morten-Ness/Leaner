import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem powersMulHom_apply (x : M) (n : Multiplicative ℕ) : powersMulHom M x n = x ^ n.toAdd := rfl


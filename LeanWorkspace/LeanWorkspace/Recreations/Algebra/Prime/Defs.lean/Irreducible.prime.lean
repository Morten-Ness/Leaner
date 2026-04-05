import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : Prime a := irr.prime_of_isPrimal (DecompositionMonoid.primal a)


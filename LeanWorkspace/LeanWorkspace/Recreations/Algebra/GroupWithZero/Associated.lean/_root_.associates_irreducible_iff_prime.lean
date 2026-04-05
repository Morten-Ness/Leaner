import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem _root_.associates_irreducible_iff_prime [DecompositionMonoid M] {p : Associates M} :
    Irreducible p ↔ Prime p := irreducible_iff_prime


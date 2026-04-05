import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M] {p : M}

theorem irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Prime a := ⟨Irreducible.prime, Prime.irreducible⟩


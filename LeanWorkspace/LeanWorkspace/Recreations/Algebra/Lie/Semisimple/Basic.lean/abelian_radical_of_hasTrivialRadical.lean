import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.radical_eq_bot]; exact LieIdeal.isLieAbelian_of_trivial ..


import Mathlib

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

theorem LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0


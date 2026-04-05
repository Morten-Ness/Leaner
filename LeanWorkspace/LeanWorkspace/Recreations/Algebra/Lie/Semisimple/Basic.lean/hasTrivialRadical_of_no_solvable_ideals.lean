import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable I → I = ⊥) :
    HasTrivialRadical R L := ⟨sSup_eq_bot.mpr h⟩


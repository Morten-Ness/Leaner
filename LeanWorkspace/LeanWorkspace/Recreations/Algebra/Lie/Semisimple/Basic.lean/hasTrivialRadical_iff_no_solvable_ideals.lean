import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable I → I = ⊥ := ⟨@LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, LieAlgebra.hasTrivialRadical_of_no_solvable_ideals⟩


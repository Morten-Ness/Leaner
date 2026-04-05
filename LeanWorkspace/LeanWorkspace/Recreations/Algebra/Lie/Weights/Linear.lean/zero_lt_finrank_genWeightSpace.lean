import Mathlib

variable (k R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
  [LieRing.IsNilpotent L]

theorem zero_lt_finrank_genWeightSpace {χ : L → R} (hχ : genWeightSpace M χ ≠ ⊥) :
    0 < finrank R (genWeightSpace M χ) := by
  rwa [← LieSubmodule.nontrivial_iff_ne_bot, ← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank,
    Nat.cast_pos] at hχ


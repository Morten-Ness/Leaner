import Mathlib

variable (R L M : Type*)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

theorem LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M]
    (N : LieSubmodule R L M) [Nontrivial N] :
    N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left <| (nontrivial_iff_ne_bot R L M).mp inferInstance


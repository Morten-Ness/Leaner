import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem map_incl_lt_iff_lt_top {N' : LieSubmodule R L N} :
    N'.map (LieSubmodule.incl N) < N ↔ N' < ⊤ := by
  convert (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp


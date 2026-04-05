import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem map_incl_le {N' : LieSubmodule R L N} :
    N'.map N.incl ≤ N := by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top


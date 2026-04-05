import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem map_restrictLie_incl_top [LieAlgebra R L] (H : LieSubalgebra R L) :
    (⊤ : LieSubmodule R H N).map (N.incl.restrictLie H) = N.restr H := by
  ext; simp


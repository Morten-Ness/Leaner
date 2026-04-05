import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem map_incl_top : (⊤ : LieSubmodule R L N).map N.incl = N := by simp


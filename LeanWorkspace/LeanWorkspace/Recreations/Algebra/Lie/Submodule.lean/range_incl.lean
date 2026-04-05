import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem range_incl : N.incl.range = N := by
  simp only [← LieSubmodule.toSubmodule_inj, LieModuleHom.toSubmodule_range, LieSubmodule.incl_coe]
  rw [Submodule.range_subtype]


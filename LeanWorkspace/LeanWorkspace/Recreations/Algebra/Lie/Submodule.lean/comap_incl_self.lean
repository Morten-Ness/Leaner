import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (N : LieSubmodule R L M)

theorem comap_incl_self : LieSubmodule.comap N.incl N = ⊤ := by
  simp only [← LieSubmodule.toSubmodule_inj, LieSubmodule.toSubmodule_comap, LieSubmodule.incl_coe, LieSubmodule.top_toSubmodule]
  rw [Submodule.comap_subtype_self]


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem sInf_toSubmodule_eq_iInf (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = ⨅ N ∈ S, (N : Submodule R M) := by
  rw [LieSubmodule.sInf_toSubmodule, ← Set.image, sInf_image]


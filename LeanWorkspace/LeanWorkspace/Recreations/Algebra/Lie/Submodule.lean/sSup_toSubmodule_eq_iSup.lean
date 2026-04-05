import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem sSup_toSubmodule_eq_iSup (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = ⨆ N ∈ S, (N : Submodule R M) := by
  rw [LieSubmodule.sSup_toSubmodule, ← Set.image, sSup_image]


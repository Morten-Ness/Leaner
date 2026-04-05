import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem iSup_toSubmodule {ι} (p : ι → LieSubmodule R L M) :
    (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M) := by
  rw [iSup, LieSubmodule.sSup_toSubmodule]; LieSubmodule.ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]


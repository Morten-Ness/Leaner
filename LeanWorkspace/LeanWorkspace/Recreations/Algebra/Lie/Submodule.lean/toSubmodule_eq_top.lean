import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem toSubmodule_eq_top : (N : Submodule R M) = ⊤ ↔ N = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule]


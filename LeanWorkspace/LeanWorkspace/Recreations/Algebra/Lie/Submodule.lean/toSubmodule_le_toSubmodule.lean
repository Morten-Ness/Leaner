import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem toSubmodule_le_toSubmodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' := Iff.rfl


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem sSup_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s ∈ S} := rfl


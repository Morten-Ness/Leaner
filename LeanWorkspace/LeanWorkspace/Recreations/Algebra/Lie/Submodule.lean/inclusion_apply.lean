import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (h : N ≤ N')

theorem inclusion_apply (m : N) : LieSubmodule.inclusion h m = ⟨m.1, h m.2⟩ := rfl


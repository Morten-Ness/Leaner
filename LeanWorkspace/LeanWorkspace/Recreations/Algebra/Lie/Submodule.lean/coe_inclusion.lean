import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (h : N ≤ N')

theorem coe_inclusion (m : N) : (LieSubmodule.inclusion h m : M) = m := rfl


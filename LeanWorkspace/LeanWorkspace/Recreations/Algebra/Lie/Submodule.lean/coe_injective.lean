import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem coe_injective : Function.Injective ((↑) : LieSubmodule R L M → Set M) := SetLike.coe_injective


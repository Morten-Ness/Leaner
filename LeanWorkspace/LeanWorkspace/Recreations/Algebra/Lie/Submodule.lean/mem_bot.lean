import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 := mem_singleton_iff


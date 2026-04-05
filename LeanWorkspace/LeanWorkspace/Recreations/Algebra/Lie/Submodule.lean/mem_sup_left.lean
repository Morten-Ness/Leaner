import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_sup_left {x : M} (hx : x ∈ N) : x ∈ N ⊔ N' := le_sup_left (a := N) hx


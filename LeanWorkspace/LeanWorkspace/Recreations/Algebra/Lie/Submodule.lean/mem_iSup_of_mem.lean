import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_iSup_of_mem {ι} {b : M} {N : ι → LieSubmodule R L M} (i : ι) (h : b ∈ N i) :
    b ∈ ⨆ i, N i := (le_iSup N i) h


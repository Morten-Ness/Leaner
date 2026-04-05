import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem span_iUnion {ι} (s : ι → Set M) : LieSubmodule.lieSpan R L (⋃ i, s i) = ⨆ i, LieSubmodule.lieSpan R L (s i) := (LieSubmodule.gi R L M).gc.l_iSup


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem lieSpan_eq (N : LieSubmodule R L M) : LieSubmodule.lieSpan R L (N : Set M) = N := le_antisymm (LieSubmodule.lieSpan_le.mpr rfl.subset) LieSubmodule.subset_lieSpan


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem lieSpan_mono {t : Set M} (h : s ⊆ t) : LieSubmodule.lieSpan R L s ≤ LieSubmodule.lieSpan R L t := by
  rw [LieSubmodule.lieSpan_le]
  exact Subset.trans h LieSubmodule.subset_lieSpan


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem lieSpan_le {N} : LieSubmodule.lieSpan R L s ≤ N ↔ s ⊆ N := by
  constructor
  · exact Subset.trans LieSubmodule.subset_lieSpan
  · intro hs m hm; rw [LieSubmodule.mem_lieSpan] at hm; exact hm _ hs


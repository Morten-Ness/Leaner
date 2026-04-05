import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ LieSubmodule.lieSpan R L s := by
  rw [Submodule.span_le]
  apply LieSubmodule.subset_lieSpan


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem span_univ : LieSubmodule.lieSpan R L (Set.univ : Set M) = ⊤ := eq_top_iff.2 <| SetLike.le_def.2 <| LieSubmodule.subset_lieSpan


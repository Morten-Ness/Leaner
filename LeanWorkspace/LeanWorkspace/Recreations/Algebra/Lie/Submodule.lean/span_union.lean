import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem span_union (s t : Set M) : LieSubmodule.lieSpan R L (s ∪ t) = LieSubmodule.lieSpan R L s ⊔ LieSubmodule.lieSpan R L t := (LieSubmodule.gi R L M).gc.l_sup


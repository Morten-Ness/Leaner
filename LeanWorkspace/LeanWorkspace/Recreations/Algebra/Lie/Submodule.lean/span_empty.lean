import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem span_empty : LieSubmodule.lieSpan R L (∅ : Set M) = ⊥ := (LieSubmodule.gi R L M).gc.l_bot


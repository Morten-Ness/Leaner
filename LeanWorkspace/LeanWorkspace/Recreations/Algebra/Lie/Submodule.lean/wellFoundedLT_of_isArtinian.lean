import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem wellFoundedLT_of_isArtinian [IsArtinian R M] : WellFoundedLT (LieSubmodule R L M) := RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding


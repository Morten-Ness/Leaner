import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

theorem lowerCentralSeries_succ :
    LieModule.lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), LieModule.lowerCentralSeries R L M k⁆ := LieSubmodule.lcs_succ (⊤ : LieSubmodule R L M) k


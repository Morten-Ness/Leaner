import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem map_mk'_eq_bot_le : map (LieSubmodule.Quotient.mk' N) N' = ⊥ ↔ N' ≤ N := by
  rw [← LieModuleHom.le_ker_iff_map, LieSubmodule.Quotient.mk'_ker]


import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem range_mk' : LieModuleHom.range (LieSubmodule.Quotient.mk' N) = ⊤ := by
  simp [LieModuleHom.range_eq_top]


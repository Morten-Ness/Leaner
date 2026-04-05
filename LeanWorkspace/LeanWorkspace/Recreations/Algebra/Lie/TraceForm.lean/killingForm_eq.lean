import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (I : LieIdeal R L)

variable [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]

theorem killingForm_eq :
    killingForm R I = (killingForm R L).restrict I := LieSubmodule.traceForm_eq_of_le_idealizer I I <| by simp


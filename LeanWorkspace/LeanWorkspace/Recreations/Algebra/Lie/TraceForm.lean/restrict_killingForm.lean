import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (I : LieIdeal R L)

theorem restrict_killingForm :
    (killingForm R L).restrict I = LieModule.traceForm R I L := rfl


import Mathlib

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

theorem restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L := rfl


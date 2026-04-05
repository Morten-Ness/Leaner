import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (I : LieIdeal R L)

theorem coe_killingCompl_top :
    LieIdeal.killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext x
  simp [LinearMap.ext_iff, LinearMap.BilinForm.IsOrtho, LieModule.traceForm_comm R L L x]


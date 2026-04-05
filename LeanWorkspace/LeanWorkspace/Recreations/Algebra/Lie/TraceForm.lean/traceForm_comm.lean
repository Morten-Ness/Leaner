import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_comm (x y : L) : LieModule.traceForm R L M x y = LieModule.traceForm R L M y x := LinearMap.trace_mul_comm R (φ x) (φ y)


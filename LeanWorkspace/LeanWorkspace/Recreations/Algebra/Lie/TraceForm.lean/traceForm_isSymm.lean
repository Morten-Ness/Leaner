import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_isSymm : LinearMap.IsSymm (LieModule.traceForm R L M) := ⟨LieModule.traceForm_comm R L M⟩


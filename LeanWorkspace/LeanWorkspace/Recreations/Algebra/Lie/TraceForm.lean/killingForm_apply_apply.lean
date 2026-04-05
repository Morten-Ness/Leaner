import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem killingForm_apply_apply (x y : L) : killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y) := LieModule.traceForm_apply_apply R L L x y


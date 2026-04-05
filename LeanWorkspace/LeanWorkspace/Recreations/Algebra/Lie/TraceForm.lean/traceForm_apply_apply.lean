import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_apply_apply (x y : L) :
    LieModule.traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) := rfl


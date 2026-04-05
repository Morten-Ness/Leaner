import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_lieSubalgebra_mk_right (L' : LieSubalgebra R L) {x : L'} {y : L} (hy : y ∈ L') :
    LieModule.traceForm R L' M x ⟨y, hy⟩ = LieModule.traceForm R L M x y := rfl


import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_lieSubalgebra_mk_left (L' : LieSubalgebra R L) {x : L} (hx : x ∈ L') (y : L') :
    LieModule.traceForm R L' M ⟨x, hx⟩ y = LieModule.traceForm R L M x y := rfl


import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieSubalgebra.toEnd_mk (K : LieSubalgebra R L) {x : L} (hx : x ∈ K) :
    LieModule.toEnd R K M ⟨x, hx⟩ = LieModule.toEnd R L M x := rfl


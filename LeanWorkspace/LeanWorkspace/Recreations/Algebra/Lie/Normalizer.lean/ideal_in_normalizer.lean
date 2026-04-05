import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (H : LieSubalgebra R L)

theorem ideal_in_normalizer {x y : L} (hx : x ∈ H.normalizer) (hy : y ∈ H) : ⁅x, y⁆ ∈ H := by
  rw [← lie_skew, neg_mem_iff (G := L)]
  exact hx ⟨y, hy⟩


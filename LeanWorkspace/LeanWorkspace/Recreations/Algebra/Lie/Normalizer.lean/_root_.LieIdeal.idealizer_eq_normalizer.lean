import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (N : LieSubmodule R L M) {N₁ N₂ : LieSubmodule R L M}

theorem _root_.LieIdeal.idealizer_eq_normalizer (I : LieIdeal R L) :
    I.idealizer = I.normalizer := by
  ext x; exact forall_congr' fun y ↦ by simp only [← lie_skew x y, neg_mem_iff]


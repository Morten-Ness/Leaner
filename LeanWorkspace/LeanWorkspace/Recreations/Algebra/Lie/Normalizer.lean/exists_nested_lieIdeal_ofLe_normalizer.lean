import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (H : LieSubalgebra R L)

theorem exists_nested_lieIdeal_ofLe_normalizer {K : LieSubalgebra R L} (h₁ : H ≤ K)
    (h₂ : K ≤ H.normalizer) : ∃ I : LieIdeal R K, (I : LieSubalgebra R K) = ofLe h₁ := by
  rw [exists_nested_lieIdeal_coe_eq_iff]
  exact fun x y hx hy => LieSubalgebra.ideal_in_normalizer (h₂ hx) hy


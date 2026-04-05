import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

theorem genWeightSpace_le_genWeightSpaceChain {k : ℤ} (hk : k ∈ Ioo p q) :
    genWeightSpace M (k • χ₁ + χ₂) ≤ LieModule.genWeightSpaceChain M χ₁ χ₂ p q := le_biSup (fun i ↦ genWeightSpace M (i • χ₁ + χ₂)) hk


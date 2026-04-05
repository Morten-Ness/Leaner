import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

theorem genWeightSpaceChain_neg :
    LieModule.genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = LieModule.genWeightSpaceChain M χ₁ χ₂ p q := by
  let e : ℤ ≃ ℤ := neg_involutive.toPerm
  simp_rw [LieModule.genWeightSpaceChain, ← e.biSup_comp (Ioo p q)]
  simp [e, -mem_Ioo]


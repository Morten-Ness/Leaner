import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

theorem lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H]
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H (-α))
    {y : M} (hy : y ∈ LieModule.genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ LieModule.genWeightSpaceChain M α χ p q := by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← LieModule.genWeightSpaceChain_neg] at hy ⊢
  exact LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy


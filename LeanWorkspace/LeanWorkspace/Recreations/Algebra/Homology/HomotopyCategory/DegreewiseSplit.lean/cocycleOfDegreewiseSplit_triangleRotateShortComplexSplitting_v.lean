import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C]

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

variable [HasBinaryBiproducts C]

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v (p : ℤ) :
    (CochainComplex.cocycleOfDegreewiseSplit _ (CochainComplex.mappingCone.triangleRotateShortComplexSplitting φ)).1.v p _ rfl =
      -φ.f _ := by
  simp [CochainComplex.cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]


import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C]

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

include hn₁ in
theorem quasiIsoAt_π (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i : ℤ) (hi : CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n₀ := by lia) :
    QuasiIsoAt (π K L n₁) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i := by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i - 1) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i - 1) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.isIso_π_f ..
    have : IsIso φ.τ₂ := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.isIso_π_f ..
    have : IsIso φ.τ₃ := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.isIso_π_f ..
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have : homologyMap (biprod.inl : _ ⟶ mid K L n₁) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i = 0 :=
      (ShortComplex.isZero_homology_of_isZero_X₂ _
        (isZero_single_obj_X (.up ℤ) _ _ _ (by lia))).eq_of_src _ _
    refine ⟨homologyMap (σ K L n₁) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i, ?_, ?_⟩
    · simp [← homologyMap_id, ← biprod.total, homologyMap_comp, this]
    · simp [← homologyMap_comp, homologyMap_id]


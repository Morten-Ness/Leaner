import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem step₁ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n₀, QuasiIsoAt f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₀ F ∧ isIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) :=
  ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi ↦ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.quasiIsoAt_ι f n₀ n₁ hn₁ hf CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi,
    fun CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi ↦ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.isIso_π_f K L n₁ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (by lia),
    inferInstance⟩


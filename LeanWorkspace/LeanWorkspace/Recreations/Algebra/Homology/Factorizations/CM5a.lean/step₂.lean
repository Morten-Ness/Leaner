import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem step₂ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n₀, QuasiIsoAt f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i) [Mono (homologyMap f n₁)] (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₁ F :=
  ⟨.mk { mid := mid f n₁, ι := ι f n₁, π := π f n₁}
    ⟨inferInstance, CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.degreewiseEpiWithInjectiveKernel_π f n₁⟩,
    fun CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi ↦ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.quasiIsoAt_ι f n₁ (fun j hj ↦ hf j (by lia)) _ hi,
    CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.isIso_π_f f n₁⟩

public lemma step [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n₀, QuasiIsoAt f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₀ F := by
  obtain ⟨F₁, h₁, h₂, _⟩ := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁ f n₀ n₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ h₁
  refine ⟨.mk { mid := F₂.obj.mid, ι := F₂.obj.ι, π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi ↦ ?_⟩⟩
  have := h₂ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi
  have := h₄ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (by lia)
  dsimp
  infer_instance


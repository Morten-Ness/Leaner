import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

variable (hf : ∀ i < n, QuasiIsoAt f i)

theorem quasiIsoAt_ι [Mono f] [Mono (homologyMap f n)] (q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (ι f n) q := by
  obtain hq | rfl := hq.lt_or_eq'
  · have := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.quasiIsoAt_π f n q hq
    rw [← quasiIsoAt_iff_comp_right _ (π f n), mappingCocone.lift_fst]
    exact hf q hq
  · have := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.mono_homologyMap_π f n n (by lia)
    have : Mono (homologyMap (mappingCocone.triangle (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).mor₁ n) :=
      by dsimp; infer_instance
    have h₁ := (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.exact_homologyShortComplex f n).fIsKernel
    have h₂ := (CochainComplex.homologyMap_exact₂_of_distTriang _
      (DerivedCategory.mappingCocone_triangle_distinguished (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)) n).fIsKernel
    have : homologyMap (ι f n) n = (IsLimit.conePointUniqueUpToIso h₁ h₂).hom := by
      simp [← cancel_mono (homologyMap (π f n) n),
        dsimp% IsLimit.conePointUniqueUpToIso_hom_comp h₁ h₂ .zero,
        ← homologyMap_comp, mappingCocone.lift_fst]
    rw [quasiIsoAt_iff_isIso_homologyMap, this]
    infer_instance


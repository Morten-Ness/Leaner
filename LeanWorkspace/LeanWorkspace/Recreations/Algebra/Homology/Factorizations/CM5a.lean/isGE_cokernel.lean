import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

variable (hf : ∀ i < n, QuasiIsoAt f i)

omit [EnoughInjectives C] in
theorem isGE_cokernel [Mono f] [Mono (homologyMap f n)] : (cokernel f).IsGE n := by
  rw [isGE_iff]
  intro CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi
  rw [exactAt_iff_isZero_homology]
  refine ((CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.shortExact f).homology_exact₃ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1) (by simp)).isZero_X₂ ?_ ?_
  · have := hf CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi
    rw [← ((CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.shortExact f).homology_exact₂ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i).epi_f_iff]
    infer_instance
  · rw [← ((CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.shortExact f).homology_exact₁ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1) (by simp)).mono_g_iff]
    by_cases hi' : CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1 < n
    · have := hf (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1) (by lia)
      infer_instance
    · obtain rfl : n = CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i + 1 := by lia
      infer_instance


import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem isIso_π_f (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i : ℤ) (hi : CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n) : IsIso ((π f n).f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i) := by
  refine ⟨(mappingCocone.inl (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).v CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (add_zero CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i), ?_, by simp⟩
  simp [← mappingCocone.id_X (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i - 1) (by lia),
    (isZero_single_obj_X _ _ _ _ (by lia)).eq_of_src
      ((mappingCocone.inr (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n)).1.v (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i - 1) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i (by lia)) 0]


import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C]

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

theorem isIso_π_f (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i : ℤ) (hi : CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≠ n₁ := by lia) :
    IsIso ((π K L n₁).f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i) := by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_tgt
  · simp


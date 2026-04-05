import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C]

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

variable (hf : ∀ i ≤ n₀, QuasiIsoAt f i)

include hn₁ hf in
theorem quasiIsoAt_ι (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i : ℤ) (hi : CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≤ n₀) :
    QuasiIsoAt (ι f n₁) CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i := by
  have := CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.quasiIsoAt_π K L n₀ n₁ hn₁ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi
  rw [← quasiIsoAt_iff_comp_right _ (π K L n₁), CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.ι_π]
  exact hf CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i hi


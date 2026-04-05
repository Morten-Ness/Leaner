import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem comp_α_f (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i : ℤ) : f.f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i ≫ (CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n).f CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₁.i = 0 := by simp [← comp_f]


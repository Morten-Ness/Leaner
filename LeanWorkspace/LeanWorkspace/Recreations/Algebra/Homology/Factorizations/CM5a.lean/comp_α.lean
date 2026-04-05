import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C] (n : ℤ)

theorem comp_α : f ≫ CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α f n = 0 := by simp [CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step₂.α]


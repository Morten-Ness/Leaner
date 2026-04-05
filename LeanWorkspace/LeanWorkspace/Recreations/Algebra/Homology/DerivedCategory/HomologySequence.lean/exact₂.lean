import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem exact₂ :
    (ShortComplex.mk ((DerivedCategory.homologyFunctor C n₀).map T.mor₁) ((DerivedCategory.homologyFunctor C n₀).map T.mor₂)
      (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
        Functor.map_zero])).Exact := (DerivedCategory.homologyFunctor C 0).homologySequence_exact₂ _ hT _


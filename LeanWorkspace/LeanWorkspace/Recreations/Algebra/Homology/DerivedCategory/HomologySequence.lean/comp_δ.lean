import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem comp_δ (h : n₀ + 1 = n₁ := by lia) :
    (DerivedCategory.homologyFunctor C n₀).map T.mor₂ ≫ DerivedCategory.HomologySequence.δ T n₀ n₁ h = 0 :=
  (DerivedCategory.homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h


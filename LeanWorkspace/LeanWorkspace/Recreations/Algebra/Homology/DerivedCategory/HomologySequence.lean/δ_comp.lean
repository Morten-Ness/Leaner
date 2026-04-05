import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem δ_comp (h : n₀ + 1 = n₁ := by lia) :
    DerivedCategory.HomologySequence.δ T n₀ n₁ h ≫ (DerivedCategory.homologyFunctor C n₁).map T.mor₁ = 0 :=
  (DerivedCategory.homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h


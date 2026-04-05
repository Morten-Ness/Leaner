import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n₀ n₁ : ℤ)

theorem exact₁ (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (DerivedCategory.HomologySequence.δ_comp T hT n₀ n₁ h)).Exact :=
  (DerivedCategory.homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h


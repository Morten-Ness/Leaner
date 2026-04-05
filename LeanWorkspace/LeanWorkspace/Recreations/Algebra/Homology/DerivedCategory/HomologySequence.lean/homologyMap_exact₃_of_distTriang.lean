import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_exact₃_of_distTriang (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (ShortComplex.mk _ _ (CochainComplex.homologyMap_homologyδOfTriangle T hT n₀ n₁ h)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₃ _ hT n₀ n₁ h)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)


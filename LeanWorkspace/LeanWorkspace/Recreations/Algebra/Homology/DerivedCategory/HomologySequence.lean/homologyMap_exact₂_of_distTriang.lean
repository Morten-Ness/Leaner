import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_exact₂_of_distTriang (n : ℤ) :
    (ShortComplex.mk _ _ (CochainComplex.homologyMap_comp_eq_zero_of_distTriang T hT n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (DerivedCategory.HomologySequence.exact₂ _ hT n)
  exact ShortComplex.isoMk
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)
    ((DerivedCategory.homologyFunctorFactors _ _).app _)


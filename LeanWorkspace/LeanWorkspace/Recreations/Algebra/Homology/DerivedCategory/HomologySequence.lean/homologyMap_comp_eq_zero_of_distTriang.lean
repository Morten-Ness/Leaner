import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_comp_eq_zero_of_distTriang (n : ℤ) :
    homologyMap T.mor₁ n ≫ homologyMap T.mor₂ n = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    ← DerivedCategory.homologyFunctorFactors_hom_naturality,
    ← Functor.map_comp_assoc, dsimp% comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero,
    Limits.zero_comp, Limits.comp_zero]


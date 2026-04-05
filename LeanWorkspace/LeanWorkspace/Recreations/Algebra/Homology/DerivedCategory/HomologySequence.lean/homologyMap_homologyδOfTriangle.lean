import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_homologyδOfTriangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    homologyMap T.mor₂ n₀ ≫ CochainComplex.homologyδOfTriangle T n₀ n₁ h = 0 := by
  simp [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    ← DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    reassoc_of% dsimp% DerivedCategory.HomologySequence.comp_δ _ hT n₀ n₁ h]


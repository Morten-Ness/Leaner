import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

variable (hT : DerivedCategory.Q.mapTriangle.obj T ∈ distTriang _)

set_option backward.isDefEq.respectTransparency false in
theorem homologyδOfTriangle_homologyMap (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    CochainComplex.homologyδOfTriangle T n₀ n₁ h ≫ homologyMap T.mor₁ n₁ = 0 := by
  rw [← cancel_epi ((DerivedCategory.homologyFunctorFactors _ _).hom.app _),
    homologyFunctorFactors_hom_app_homologyδOfTriangle_assoc ..,
    ← DerivedCategory.homologyFunctorFactors_hom_naturality]
  dsimp
  rw [reassoc_of% dsimp% DerivedCategory.HomologySequence.δ_comp _ hT n₀ n₁ h]
  simp


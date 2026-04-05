import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

variable {C} (T : Triangle (CochainComplex C ℤ))

set_option backward.isDefEq.respectTransparency false in
theorem homologyFunctorFactors_hom_app_homologyδOfTriangle
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁ := by lia) :
    (DerivedCategory.homologyFunctorFactors C n₀).hom.app T.obj₃ ≫
      CochainComplex.homologyδOfTriangle T n₀ n₁ h =
    DerivedCategory.HomologySequence.δ
      (DerivedCategory.Q.mapTriangle.obj T) n₀ n₁ h ≫
        (DerivedCategory.homologyFunctorFactors C n₁).hom.app T.obj₁ := by
  dsimp [DerivedCategory.HomologySequence.δ]
  rw [dsimp% [ShiftedHom.map]
      DerivedCategory.shiftMap_homologyFunctor_map_Q T.mor₃ n₀ n₁ (by lia)]
  simp [Functor.shiftMap, homologyFunctor_shift, CochainComplex.homologyδOfTriangle]


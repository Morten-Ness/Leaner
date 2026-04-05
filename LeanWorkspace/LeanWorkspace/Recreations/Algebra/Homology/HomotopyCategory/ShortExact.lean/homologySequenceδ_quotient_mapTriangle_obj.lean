import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem homologySequenceδ_quotient_mapTriangle_obj
    (T : Triangle (CochainComplex C ℤ)) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (homologyFunctor C (up ℤ) 0).homologySequenceδ
        ((quotient C (up ℤ)).mapTriangle.obj T) n₀ n₁ h =
      (homologyFunctorFactors C (up ℤ) n₀).hom.app _ ≫
        (HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftMap T.mor₃ n₀ n₁ (by lia) ≫
        (homologyFunctorFactors C (up ℤ) n₁).inv.app _ := by
  apply homologyFunctor_shiftMap


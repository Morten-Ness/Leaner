import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

theorem homologyFunctor_shiftMap
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧) (a a' : ℤ) (h : n + a = a') :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (ShiftedHom.map f (quotient _ _)) a a' h =
        (homologyFunctorFactors _ _ a).hom.app K ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap f a a' h ≫
            (homologyFunctorFactors _ _ a').inv.app L := by
  apply Functor.ShiftSequence.induced_shiftMap


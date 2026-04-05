import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

theorem homologyShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
      ((quotient _ _).obj K) =
    (homologyFunctor _ _ a).map (((quotient _ _).commShiftIso n).inv.app K) ≫
      (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
      (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj


import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b c h =
      CochainComplex.shiftFunctorAdd' C a b c h := by
  ext
  simp only [CochainComplex.shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]


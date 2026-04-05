import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ = CochainComplex.shiftFunctorZero' C 0 rfl := by
  ext
  rw [CochainComplex.shiftFunctorZero_hom_app_f, shiftFunctorZero'_hom_app_f]


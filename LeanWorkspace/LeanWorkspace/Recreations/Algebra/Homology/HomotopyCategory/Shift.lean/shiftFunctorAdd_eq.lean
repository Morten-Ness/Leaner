import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b = CochainComplex.shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd, CochainComplex.shiftFunctorAdd'_eq]


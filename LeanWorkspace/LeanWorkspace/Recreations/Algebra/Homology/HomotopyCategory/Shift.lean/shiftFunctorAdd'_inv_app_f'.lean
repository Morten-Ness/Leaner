import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctorAdd'_inv_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, CochainComplex.shiftFunctorAdd_inv_app_f]


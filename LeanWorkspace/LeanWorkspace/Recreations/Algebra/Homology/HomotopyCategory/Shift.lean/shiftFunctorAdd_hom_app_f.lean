import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctorAdd_hom_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := by
  tauto


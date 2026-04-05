import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctor_obj_d' (K : CochainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl


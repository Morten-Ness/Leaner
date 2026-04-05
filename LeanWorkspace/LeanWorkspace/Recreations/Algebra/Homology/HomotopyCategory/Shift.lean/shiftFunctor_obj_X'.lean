import Mathlib

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem shiftFunctor_obj_X' (K : CochainComplex C ℤ) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).X p = K.X (p + n) := rfl


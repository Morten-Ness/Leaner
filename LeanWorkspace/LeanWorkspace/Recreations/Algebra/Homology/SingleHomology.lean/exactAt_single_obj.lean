import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem exactAt_single_obj (A : C) (i : ι) (hi : i ≠ j) :
    ExactAt ((single C c j).obj A) i := ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)


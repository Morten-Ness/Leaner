import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem isZero_single_obj_homology (A : C) (i : ι) (hi : i ≠ j) :
    IsZero (((single C c j).obj A).homology i) := by
  simpa only [← exactAt_iff_isZero_homology]
    using HomologicalComplex.exactAt_single_obj c j A i hi


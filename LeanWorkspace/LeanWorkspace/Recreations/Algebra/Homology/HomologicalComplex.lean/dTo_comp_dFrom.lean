import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dTo_comp_dFrom (j : ι) : C.dTo j ≫ C.dFrom j = 0 := C.d_comp_d _ _ _


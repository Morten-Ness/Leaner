import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem single_obj_d (j : ι) (A : V) (k l : ι) :
    ((HomologicalComplex.single V c j).obj A).d k l = 0 := rfl


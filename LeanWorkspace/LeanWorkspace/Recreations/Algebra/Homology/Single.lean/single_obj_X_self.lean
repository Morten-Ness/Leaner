import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem single_obj_X_self (j : ι) (A : V) :
    ((HomologicalComplex.single V c j).obj A).X j = A := if_pos rfl


import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem isZero_single_comp_eval (j i : ι) (hi : i ≠ j) : IsZero (HomologicalComplex.single V c j ⋙ eval V c i) := Functor.isZero _ (fun _ ↦ HomologicalComplex.isZero_single_obj_X c _ _ _ hi)


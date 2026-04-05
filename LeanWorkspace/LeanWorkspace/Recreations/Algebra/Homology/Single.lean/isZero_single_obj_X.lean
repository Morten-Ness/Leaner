import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem isZero_single_obj_X (j : ι) (A : V) (i : ι) (hi : i ≠ j) :
    IsZero (((HomologicalComplex.single V c j).obj A).X i) := by
  dsimp [HomologicalComplex.single]
  rw [if_neg hi]
  exact Limits.isZero_zero V


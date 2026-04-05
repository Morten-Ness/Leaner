import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem singleObjCyclesSelfIso_inv_homologyπ :
    (HomologicalComplex.singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyπ j =
      (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv := by
  simp [HomologicalComplex.singleObjCyclesSelfIso, HomologicalComplex.singleObjHomologySelfIso]


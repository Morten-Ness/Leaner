import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem homologyπ_singleObjHomologySelfIso_hom :
    ((single C c j).obj A).homologyπ j ≫ (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom =
      (HomologicalComplex.singleObjCyclesSelfIso _ _ _).hom := by
  simp [HomologicalComplex.singleObjCyclesSelfIso, HomologicalComplex.singleObjHomologySelfIso]


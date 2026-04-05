import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (HomologicalComplex.singleObjCyclesSelfIso c j A).hom ≫ (HomologicalComplex.singleObjOpcyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ ((single C c j).obj A).pOpcycles j := by
  simp [HomologicalComplex.singleObjCyclesSelfIso, HomologicalComplex.singleObjOpcyclesSelfIso]


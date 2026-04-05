import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem singleObjHomologySelfIso_inv_homologyι :
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyι j =
      (HomologicalComplex.singleObjOpcyclesSelfIso _ _ _).hom := by
  rw [← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso c j A).hom,
    singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc, homology_π_ι,
    HomologicalComplex.singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]


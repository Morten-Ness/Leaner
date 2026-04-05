import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv :
    (HomologicalComplex.singleObjCyclesSelfIso c j A).hom ≫ (HomologicalComplex.singleObjHomologySelfIso c j A).inv =
      ((single C c j).obj A).homologyπ j := by
  simp only [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]


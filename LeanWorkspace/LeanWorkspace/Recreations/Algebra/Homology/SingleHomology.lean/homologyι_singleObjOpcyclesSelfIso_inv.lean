import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem homologyι_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).homologyι j ≫ (HomologicalComplex.singleObjOpcyclesSelfIso _ _ _).inv =
      (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom := by
  rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv,
    singleObjHomologySelfIso_inv_homologyι_assoc, Iso.hom_inv_id, Iso.inv_hom_id]


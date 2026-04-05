import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (HomologicalComplex.singleObjHomologySelfIso _ _ _).hom ≫ (HomologicalComplex.singleObjOpcyclesSelfIso _ _ _).hom =
      ((single C c j).obj A).homologyι j := by
  rw [← cancel_epi (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv,
    Iso.inv_hom_id_assoc, HomologicalComplex.singleObjHomologySelfIso_inv_homologyι]


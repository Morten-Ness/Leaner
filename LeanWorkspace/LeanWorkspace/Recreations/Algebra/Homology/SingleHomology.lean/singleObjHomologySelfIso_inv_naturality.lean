import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjHomologySelfIso_inv_naturality :
    (HomologicalComplex.singleObjHomologySelfIso c j A).inv ≫ homologyMap ((single C c j).map f) j =
      f ≫ (HomologicalComplex.singleObjHomologySelfIso c j B).inv := by
  rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso c j B).hom, assoc, assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]


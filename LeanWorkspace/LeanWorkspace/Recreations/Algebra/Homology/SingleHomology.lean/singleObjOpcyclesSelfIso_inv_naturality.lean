import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjOpcyclesSelfIso_inv_naturality :
    opcyclesMap ((single C c j).map f) j ≫ (HomologicalComplex.singleObjOpcyclesSelfIso c j B).inv =
      (HomologicalComplex.singleObjOpcyclesSelfIso c j A).inv ≫ f := by
  rw [← cancel_mono (HomologicalComplex.singleObjOpcyclesSelfIso c j B).hom, assoc, assoc, Iso.inv_hom_id,
    comp_id, ← HomologicalComplex.singleObjOpcyclesSelfIso_hom_naturality, Iso.inv_hom_id_assoc]


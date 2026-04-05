import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjCyclesSelfIso_inv_naturality :
    (HomologicalComplex.singleObjCyclesSelfIso c j A).inv ≫ cyclesMap ((single C c j).map f) j =
      f ≫ (HomologicalComplex.singleObjCyclesSelfIso c j B).inv := by
  rw [← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso c j A).hom, Iso.hom_inv_id_assoc,
    ← singleObjCyclesSelfIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]


import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjCyclesSelfIso_hom_naturality :
    cyclesMap ((single C c j).map f) j ≫ (HomologicalComplex.singleObjCyclesSelfIso c j B).hom =
      (HomologicalComplex.singleObjCyclesSelfIso c j A).hom ≫ f := by
  rw [← cancel_mono (HomologicalComplex.singleObjCyclesSelfIso c j B).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, HomologicalComplex.singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_map_f_self]


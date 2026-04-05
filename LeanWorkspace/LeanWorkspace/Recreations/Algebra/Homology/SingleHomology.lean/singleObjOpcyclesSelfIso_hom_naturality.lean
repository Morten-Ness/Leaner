import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjOpcyclesSelfIso_hom_naturality :
    (HomologicalComplex.singleObjOpcyclesSelfIso c j A).hom ≫ opcyclesMap ((single C c j).map f) j =
      f ≫ (HomologicalComplex.singleObjOpcyclesSelfIso c j B).hom := by
  rw [← cancel_epi (HomologicalComplex.singleObjCyclesSelfIso c j A).hom,
    singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc, p_opcyclesMap,
    single_map_f_self, assoc, assoc, HomologicalComplex.singleObjCyclesSelfIso_hom,
    HomologicalComplex.singleObjOpcyclesSelfIso_hom, assoc]


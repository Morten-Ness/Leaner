import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

variable {B : C} (f : A ⟶ B)

theorem singleObjHomologySelfIso_hom_naturality :
    homologyMap ((single C c j).map f) j ≫ (HomologicalComplex.singleObjHomologySelfIso c j B).hom =
      (HomologicalComplex.singleObjHomologySelfIso c j A).hom ≫ f := by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j),
    homologyπ_naturality_assoc, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc]


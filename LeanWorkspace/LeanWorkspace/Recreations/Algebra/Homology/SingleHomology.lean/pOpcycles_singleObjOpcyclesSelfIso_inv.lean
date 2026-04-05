import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

variable (A : C)

theorem pOpcycles_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).pOpcycles j ≫ (HomologicalComplex.singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjXSelf c j A).hom := by
  have := ((single C c j).obj A).isIso_iCycles j _ rfl (by simp)
  rw [← cancel_epi (((single C c j).obj A).iCycles j),
    ← HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom, HomologicalComplex.singleObjCyclesSelfIso_hom]


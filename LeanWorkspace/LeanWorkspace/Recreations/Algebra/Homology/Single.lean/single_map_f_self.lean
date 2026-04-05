import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

theorem single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
    ((HomologicalComplex.single V c j).map f).f j = (HomologicalComplex.singleObjXSelf c j A).hom ≫
      f ≫ (HomologicalComplex.singleObjXSelf c j B).inv := by
  dsimp [HomologicalComplex.single]
  rw [dif_pos rfl]
  rfl


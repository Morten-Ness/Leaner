import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem single₀_map_f_zero {A B : V} (f : A ⟶ B) :
    ((single₀ V).map f).f 0 = f := by
  rw [HomologicalComplex.single_map_f_self]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  rw [comp_id, id_comp]


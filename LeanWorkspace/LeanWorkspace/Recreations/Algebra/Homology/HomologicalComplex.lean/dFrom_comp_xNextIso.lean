import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dFrom_comp_xNextIso {i j : ι} (r : c.Rel i j) :
    C.dFrom i ≫ (C.xNextIso r).hom = C.d i j := by
  simp [C.dFrom_eq r]


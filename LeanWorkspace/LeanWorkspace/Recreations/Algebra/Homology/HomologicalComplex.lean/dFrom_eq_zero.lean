import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dFrom_eq_zero {i : ι} (h : ¬c.Rel i (ChainComplex.next c i)) : C.dFrom i = 0 := by
  simp [h]


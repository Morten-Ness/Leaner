import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dTo_eq_zero {j : ι} (h : ¬c.Rel (ChainComplex.prev c j) j) : C.dTo j = 0 := by
  simp [h]


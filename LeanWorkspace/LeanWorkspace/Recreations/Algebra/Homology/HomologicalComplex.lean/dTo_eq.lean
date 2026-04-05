import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dTo_eq {i j : ι} (r : c.Rel i j) : C.dTo j = (C.xPrevIso r).hom ≫ C.d i j := by
  obtain rfl := c.prev_eq' r
  exact (Category.id_comp _).symm


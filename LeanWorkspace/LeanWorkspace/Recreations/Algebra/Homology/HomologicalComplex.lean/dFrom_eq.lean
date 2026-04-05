import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dFrom_eq {i j : ι} (r : c.Rel i j) : C.dFrom i = C.d i j ≫ (C.xNextIso r).inv := by
  obtain rfl := c.next_eq' r
  exact (Category.comp_id _).symm


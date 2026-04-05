import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem xPrevIsoSelf_comp_dTo {j : ι} (h : ¬c.Rel (ChainComplex.prev c j) j) :
    (C.xPrevIsoSelf h).inv ≫ C.dTo j = 0 := by simp [h]


import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem dFrom_comp_xNextIsoSelf {i : ι} (h : ¬c.Rel i (ChainComplex.next c i)) :
    C.dFrom i ≫ (C.xNextIsoSelf h).hom = 0 := by simp [h]

-- This is not a simp lemma; the LHS already simplifies.


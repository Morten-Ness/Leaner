import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

theorem CochainComplex.exactAt_succ_single_obj (A : C) (n : ℕ) :
    ExactAt ((single₀ C).obj A) (n + 1) := HomologicalComplex.exactAt_single_obj _ _ _ _ (by simp)


import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem d_comp_d (C : HomologicalComplex V c) (i j k : ι) : C.d i j ≫ C.d j k = 0 := by
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · exact C.d_comp_d' i j k hij hjk
    · rw [C.shape j k hjk, comp_zero]
  · rw [C.shape i j hij, zero_comp]


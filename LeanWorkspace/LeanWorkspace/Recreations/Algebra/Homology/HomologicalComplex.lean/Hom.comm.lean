import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem Hom.comm {A B : HomologicalComplex V c} (f : A.Hom B) (i j : ι) :
    f.f i ≫ B.d i j = A.d i j ≫ f.f j := by
  by_cases hij : c.Rel i j
  · exact f.comm' i j hij
  · rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp]


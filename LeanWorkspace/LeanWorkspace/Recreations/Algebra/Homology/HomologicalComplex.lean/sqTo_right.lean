import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem sqTo_right (f : HomologicalComplex.Hom C₁ C₂) (j : ι) : (f.sqTo j).right = f.f j := rfl


import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem sqFrom_left (f : HomologicalComplex.Hom C₁ C₂) (i : ι) : (f.sqFrom i).left = f.f i := rfl


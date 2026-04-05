import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem sqFrom_id (C₁ : HomologicalComplex V c) (i : ι) : HomologicalComplex.Hom.sqFrom (𝟙 C₁) i = 𝟙 _ := rfl


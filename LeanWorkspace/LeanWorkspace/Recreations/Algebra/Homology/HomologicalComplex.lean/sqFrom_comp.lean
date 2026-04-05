import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

variable {C₁ C₂ C₃ : HomologicalComplex V c}

theorem sqFrom_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    HomologicalComplex.Hom.sqFrom (f ≫ g) i = HomologicalComplex.Hom.sqFrom f i ≫ HomologicalComplex.Hom.sqFrom g i := rfl


import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem comp_f {C₁ C₂ C₃ : HomologicalComplex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
    (f ≫ g).f i = f.f i ≫ g.f i := rfl


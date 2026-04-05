import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem hom_f_injective {C₁ C₂ : HomologicalComplex V c} :
    Function.Injective fun f : Hom C₁ C₂ => f.f := by cat_disch


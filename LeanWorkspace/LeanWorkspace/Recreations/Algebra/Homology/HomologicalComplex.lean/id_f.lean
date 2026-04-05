import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem id_f (C : HomologicalComplex V c) (i : ι) : Hom.f (𝟙 C) i = 𝟙 (C.X i) := rfl


import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem zero_f (C D : HomologicalComplex V c) (i : ι) : (0 : C ⟶ D).f i = 0 := rfl


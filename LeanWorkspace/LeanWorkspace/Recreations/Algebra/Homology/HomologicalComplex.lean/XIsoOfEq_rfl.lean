import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {V} {c : ComplexShape ι}

theorem XIsoOfEq_rfl (K : HomologicalComplex V c) (p : ι) :
    K.XIsoOfEq (rfl : p = p) = Iso.refl _ := rfl


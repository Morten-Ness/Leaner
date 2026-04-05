import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem congr_hom {C D : HomologicalComplex V c} {f g : C ⟶ D} (w : f = g) (i : ι) :
    f.f i = g.f i := congr_fun (congr_arg Hom.f w) i


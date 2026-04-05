import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem hom_ext {C D : HomologicalComplex V c} (f g : C ⟶ D)
    (h : ∀ i, f.f i = g.f i) : f = g := by
  apply Hom.ext
  funext
  apply h


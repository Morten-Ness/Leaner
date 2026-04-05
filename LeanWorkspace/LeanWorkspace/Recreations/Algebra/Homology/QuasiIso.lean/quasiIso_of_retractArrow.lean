import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIso_of_retractArrow {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [∀ i, K'.HasHomology i] [∀ i, L'.HasHomology i] [QuasiIso f'] :
    QuasiIso f where
  quasiIsoAt i := quasiIsoAt_of_retract h i


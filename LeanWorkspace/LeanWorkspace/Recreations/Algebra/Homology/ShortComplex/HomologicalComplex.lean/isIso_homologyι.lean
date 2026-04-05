import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

variable (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i]

theorem isIso_homologyι : IsIso (K.homologyι i) := ShortComplex.isIso_homologyι _ (by cat_disch)


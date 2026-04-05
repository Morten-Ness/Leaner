import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem ExactAt.isZero_homology [K.HasHomology i] (h : K.ExactAt i) :
    IsZero (K.homology i) := by
  rwa [← HomologicalComplex.exactAt_iff_isZero_homology]


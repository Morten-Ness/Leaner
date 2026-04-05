import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem exactAt_iff_isZero_homology [K.HasHomology i] :
    K.ExactAt i ↔ IsZero (K.homology i) := by
  dsimp [HomologicalComplex.homology]
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]


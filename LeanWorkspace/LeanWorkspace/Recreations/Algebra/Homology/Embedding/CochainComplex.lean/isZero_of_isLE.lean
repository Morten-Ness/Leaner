import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isZero_of_isLE (n i : ℤ) (hi : n < i := by lia) [K.IsLE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isLE n i hi).isZero_homology


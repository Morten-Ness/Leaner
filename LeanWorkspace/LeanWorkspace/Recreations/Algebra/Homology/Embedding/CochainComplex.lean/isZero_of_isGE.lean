import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isZero_of_isGE (n i : ℤ) (hi : i < n := by lia) [K.IsGE n] [K.HasHomology i] :
    IsZero (K.homology i) :=
  (K.exactAt_of_isGE n i hi).isZero_homology


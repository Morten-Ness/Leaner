import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isGE_of_iso (n : ℤ) [K.IsGE n] : L.IsGE n := by
  apply isSupported_of_iso e


import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isLE_of_iso (n : ℤ) [K.IsLE n] : L.IsLE n := by
  apply isSupported_of_iso e


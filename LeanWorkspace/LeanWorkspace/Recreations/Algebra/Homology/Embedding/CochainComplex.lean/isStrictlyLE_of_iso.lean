import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyLE_of_iso (n : ℤ) [K.IsStrictlyLE n] : L.IsStrictlyLE n := by
  apply isStrictlySupported_of_iso e


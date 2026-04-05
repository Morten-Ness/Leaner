import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyGE_of_iso (n : ℤ) [K.IsStrictlyGE n] : L.IsStrictlyGE n := by
  apply isStrictlySupported_of_iso e


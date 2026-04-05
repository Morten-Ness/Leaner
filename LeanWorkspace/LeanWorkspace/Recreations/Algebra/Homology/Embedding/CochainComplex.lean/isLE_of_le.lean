import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
    K.IsLE q := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact K.exactAt_of_isLE p _


import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyLE_of_le (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
    K.IsStrictlyLE q := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyLE p _


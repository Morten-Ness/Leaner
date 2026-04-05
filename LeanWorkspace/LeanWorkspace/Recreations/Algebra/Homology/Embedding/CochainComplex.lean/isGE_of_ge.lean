import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
    K.IsGE p := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact K.exactAt_of_isGE q _


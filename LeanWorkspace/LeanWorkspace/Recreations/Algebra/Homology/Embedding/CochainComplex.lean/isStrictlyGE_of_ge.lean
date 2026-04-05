import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyGE_of_ge (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
    K.IsStrictlyGE p := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact K.isZero_of_isStrictlyGE q _


import Mathlib

variable {C : Type*} [Category* C]

variable [Preadditive C]

variable (K : CochainComplex C ℤ)

theorem isStrictlyLE_shift (n : ℤ) [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)


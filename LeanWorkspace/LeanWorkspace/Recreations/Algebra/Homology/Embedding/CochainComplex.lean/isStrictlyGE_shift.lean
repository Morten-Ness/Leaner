import Mathlib

variable {C : Type*} [Category* C]

variable [Preadditive C]

variable (K : CochainComplex C ℤ)

theorem isStrictlyGE_shift (n : ℤ) [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by lia)) (K.shiftFunctorObjXIso a i _ rfl)


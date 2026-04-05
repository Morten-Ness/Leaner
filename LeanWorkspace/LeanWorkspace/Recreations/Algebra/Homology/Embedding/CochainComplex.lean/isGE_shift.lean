import Mathlib

variable {C : Type*} [Category* C]

variable [Preadditive C]

variable (K : CochainComplex C ℤ)

variable [CategoryWithHomology C]

theorem isGE_shift (n : ℤ) [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact IsZero.of_iso (K.isZero_of_isGE n (a + i) (by lia))
    (((homologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)


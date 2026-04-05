import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

theorem ιTruncLE_naturality (n : ℤ) :
    truncLEMap φ n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ φ := by
  apply HomologicalComplex.ιTruncLE_naturality


import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem isIso_ιTruncLE_iff : IsIso (K.ιTruncLE n) ↔ K.IsStrictlyLE n := by
  apply HomologicalComplex.isIso_ιTruncLE_iff


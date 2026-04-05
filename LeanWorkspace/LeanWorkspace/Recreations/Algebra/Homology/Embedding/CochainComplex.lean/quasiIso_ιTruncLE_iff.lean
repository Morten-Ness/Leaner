import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem quasiIso_ιTruncLE_iff : QuasiIso (K.ιTruncLE n) ↔ K.IsLE n := quasiIso_ιTruncLE_iff_isSupported K (embeddingUpIntLE n)


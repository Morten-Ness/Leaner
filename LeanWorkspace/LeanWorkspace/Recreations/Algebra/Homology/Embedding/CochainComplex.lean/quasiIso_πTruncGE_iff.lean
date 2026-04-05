import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem quasiIso_πTruncGE_iff : QuasiIso (K.πTruncGE n) ↔ K.IsGE n := quasiIso_πTruncGE_iff_isSupported K (embeddingUpIntGE n)


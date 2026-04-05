import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

variable [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] (n : ℤ)

theorem isIso_πTruncGE_iff : IsIso (K.πTruncGE n) ↔ K.IsStrictlyGE n := by
  apply HomologicalComplex.isIso_πTruncGE_iff


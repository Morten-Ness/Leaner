import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C] [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]

theorem πTruncGE_naturality (n : ℤ) :
    K.πTruncGE n ≫ truncGEMap φ n = φ ≫ L.πTruncGE n := by
  apply HomologicalComplex.πTruncGE_naturality


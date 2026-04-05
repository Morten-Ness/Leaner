import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem exactAt_of_isGE (n i : ℤ) (hi : i < n := by lia) [K.IsGE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntGE n) i
    (by simpa only [notMem_range_embeddingUpIntGE_iff] using hi)


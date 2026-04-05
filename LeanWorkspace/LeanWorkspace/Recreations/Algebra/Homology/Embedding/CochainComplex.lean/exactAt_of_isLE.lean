import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem exactAt_of_isLE (n i : ℤ) (hi : n < i := by lia) [K.IsLE n] :
    K.ExactAt i :=
  exactAt_of_isSupported K (embeddingUpIntLE n) i
    (by simpa only [notMem_range_embeddingUpIntLE_iff] using hi)


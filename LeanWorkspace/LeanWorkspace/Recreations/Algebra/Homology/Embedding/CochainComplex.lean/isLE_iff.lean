import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isLE_iff (n : ℤ) :
    K.IsLE n ↔ ∀ (i : ℤ) (_ : n < i), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isLE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi


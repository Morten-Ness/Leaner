import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isGE_iff (n : ℤ) :
    K.IsGE n ↔ ∀ (i : ℤ) (_ : i < n), K.ExactAt i := by
  constructor
  · intro _ i hi
    exact K.exactAt_of_isGE n i hi
  · intro h
    refine IsSupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi


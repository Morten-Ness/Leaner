import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyLE_iff (n : ℤ) :
    K.IsStrictlyLE n ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyLE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntLE_iff] at hi
    exact h i hi


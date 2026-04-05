import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

theorem isStrictlyGE_iff (n : ℤ) :
    K.IsStrictlyGE n ↔ ∀ (i : ℤ) (_ : i < n := by lia), IsZero (K.X i) := by
  constructor
  · intro _ i hi
    exact K.isZero_of_isStrictlyGE n i hi
  · intro h
    refine IsStrictlySupported.mk (fun i hi ↦ ?_)
    rw [notMem_range_embeddingUpIntGE_iff] at hi
    exact h i hi


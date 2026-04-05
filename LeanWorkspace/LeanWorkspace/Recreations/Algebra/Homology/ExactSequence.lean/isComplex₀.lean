import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex₀ (S : CategoryTheory.ComposableArrows C 0) : S.IsComplex where
  zero i hi := by simp at hi


import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex₁ (S : CategoryTheory.ComposableArrows C 1) : S.IsComplex where
  zero i hi := by lia


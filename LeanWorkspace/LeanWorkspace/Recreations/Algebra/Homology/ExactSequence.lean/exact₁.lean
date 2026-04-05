import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact₁ (S : CategoryTheory.ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; lia


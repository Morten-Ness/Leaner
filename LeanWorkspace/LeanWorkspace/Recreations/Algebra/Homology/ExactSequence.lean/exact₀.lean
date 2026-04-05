import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact₀ (S : CategoryTheory.ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi


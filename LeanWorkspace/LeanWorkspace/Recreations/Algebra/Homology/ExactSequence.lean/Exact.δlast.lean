import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem Exact.δlast {S : CategoryTheory.ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δlast.Exact := by
  rw [CategoryTheory.ComposableArrows.exact_iff_δlast] at hS
  exact hS.1


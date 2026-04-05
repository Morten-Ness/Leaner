import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem Exact.δ₀ {S : CategoryTheory.ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δ₀.Exact := by
  rw [CategoryTheory.ComposableArrows.exact_iff_δ₀] at hS
  exact hS.2


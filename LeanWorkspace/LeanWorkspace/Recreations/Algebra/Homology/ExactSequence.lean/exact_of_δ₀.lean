import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact_of_δ₀ {S : CategoryTheory.ComposableArrows C (n + 2)}
    (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) : S.Exact := by
  rw [CategoryTheory.ComposableArrows.exact_iff_δ₀]
  constructor <;> assumption


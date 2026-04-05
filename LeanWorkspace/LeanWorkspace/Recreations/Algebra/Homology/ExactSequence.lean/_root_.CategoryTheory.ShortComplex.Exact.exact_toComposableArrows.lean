import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
    {S : ShortComplex C} (hS : S.Exact) :
    S.toComposableArrows.Exact := CategoryTheory.ComposableArrows.exact₂_mk _ _ hS


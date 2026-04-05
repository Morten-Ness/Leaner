import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem _root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows
    (S : ShortComplex C) :
    S.Exact ↔ S.toComposableArrows.Exact := (S.CategoryTheory.ComposableArrows.exact₂_iff toComposableArrows S.isComplex_toComposableArrows).symm


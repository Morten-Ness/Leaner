import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact₂_mk (S : CategoryTheory.ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
    (h : (ShortComplex.mk _ _ w).Exact) : S.Exact := (S.exact₂_iff (S.isComplex₂_mk w)).2 h


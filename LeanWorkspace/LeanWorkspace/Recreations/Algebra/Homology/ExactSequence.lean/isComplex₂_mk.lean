import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem isComplex₂_mk (S : CategoryTheory.ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) :
    S.IsComplex := S.isComplex₂_iff.2 w


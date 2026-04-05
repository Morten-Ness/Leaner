import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

set_option backward.isDefEq.respectTransparency false in
theorem _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex := -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  CategoryTheory.ComposableArrows.isComplex₂_mk _ (by simp [-Fin.reduceFinMk])


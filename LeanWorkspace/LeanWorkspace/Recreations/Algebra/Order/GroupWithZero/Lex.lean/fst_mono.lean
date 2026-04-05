import Mathlib

variable {M₀ N₀ : Type*}

theorem fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀] :
    Monotone (fst M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]


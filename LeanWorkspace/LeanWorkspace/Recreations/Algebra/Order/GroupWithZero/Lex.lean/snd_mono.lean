import Mathlib

variable {M₀ N₀ : Type*}

theorem snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀] :
    Monotone (snd M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]


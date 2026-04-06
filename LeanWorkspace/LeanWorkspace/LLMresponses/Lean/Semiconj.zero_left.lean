import Mathlib

variable {G₀ : Type*}

theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  dsimp [SemiconjBy]
  simp

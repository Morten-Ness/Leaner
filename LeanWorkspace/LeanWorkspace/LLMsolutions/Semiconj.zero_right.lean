import Mathlib

variable {G₀ : Type*}

theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  dsimp [SemiconjBy]
  rw [MulZeroClass.mul_zero, MulZeroClass.zero_mul]

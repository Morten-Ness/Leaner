import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 := SemiconjBy.zero_right a


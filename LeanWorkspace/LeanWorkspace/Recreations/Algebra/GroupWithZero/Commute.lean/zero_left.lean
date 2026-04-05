import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a := SemiconjBy.zero_left a a


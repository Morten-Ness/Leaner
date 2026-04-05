import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) := SemiconjBy.div_right hab hac


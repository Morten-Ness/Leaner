import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff₀


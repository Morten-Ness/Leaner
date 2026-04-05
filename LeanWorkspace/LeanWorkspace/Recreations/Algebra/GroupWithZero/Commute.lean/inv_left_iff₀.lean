import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff₀


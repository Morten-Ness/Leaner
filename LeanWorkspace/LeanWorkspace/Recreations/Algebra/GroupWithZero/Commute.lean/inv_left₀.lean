import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b := Commute.inv_left_iff₀.2 h


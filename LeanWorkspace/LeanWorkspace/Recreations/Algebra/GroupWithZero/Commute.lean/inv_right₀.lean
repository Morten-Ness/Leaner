import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀}

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ := Commute.inv_right_iff₀.2 h


import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : Units.mk0 (u : G₀) h = u := Units.ext rfl


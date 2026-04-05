import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem val_mk0 {a : G₀} (h : a ≠ 0) : (Units.mk0 a h : G₀) = a := rfl


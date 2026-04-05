import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem mk0_one (h := one_ne_zero) : Units.mk0 (1 : G₀) h = 1 := by
  ext
  rfl


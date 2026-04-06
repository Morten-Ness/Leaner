import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

def mk0_one (h : (1 : G₀) ≠ 0 := by simpa using (one_ne_zero : (1 : G₀) ≠ 0)) : G₀ˣ :=
  Units.mk0 1 h

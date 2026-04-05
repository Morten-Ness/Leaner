import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x := (Units.mk0 x hx).isUnit


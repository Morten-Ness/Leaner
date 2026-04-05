import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b := ⟨fun h => by injection h, fun h => Units.ext h⟩


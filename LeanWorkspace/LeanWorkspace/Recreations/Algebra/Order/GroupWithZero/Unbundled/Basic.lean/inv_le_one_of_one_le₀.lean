import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

theorem inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 := (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha


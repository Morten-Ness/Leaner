import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable [PosMulMono G₀]

theorem one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''


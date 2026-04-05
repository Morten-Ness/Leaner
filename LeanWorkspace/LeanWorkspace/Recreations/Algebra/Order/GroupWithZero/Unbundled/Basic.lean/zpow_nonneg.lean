import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [MulPosMono G₀] {n : ℤ}

theorem zpow_left_strictMonoOn₀ (hn : 0 < n) : StrictMonoOn (fun a : G₀ ↦ a ^ n) {a | 0 ≤ a} := by
  lift n to ℕ using hn.le; simpa using pow_left_strictMonoOn₀ (by lia)


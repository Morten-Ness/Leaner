import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁


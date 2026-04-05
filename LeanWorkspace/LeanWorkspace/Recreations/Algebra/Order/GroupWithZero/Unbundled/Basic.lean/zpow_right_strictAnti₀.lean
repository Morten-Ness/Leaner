import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁


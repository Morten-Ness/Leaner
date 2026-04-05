import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha


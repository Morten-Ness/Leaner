import Mathlib

variable {α : Type*}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {n : ℤ} {a b : α}

theorem zpow_le_zpow_iff_left (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b := (zpow_left_strictMono α hn).le_iff_le


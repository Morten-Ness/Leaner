import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_le_zpow_left (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_left_mono α hn h


import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_lt_zpow_right (ha : 1 < a) (h : m < n) : a ^ m < a ^ n := zpow_right_strictMono ha h


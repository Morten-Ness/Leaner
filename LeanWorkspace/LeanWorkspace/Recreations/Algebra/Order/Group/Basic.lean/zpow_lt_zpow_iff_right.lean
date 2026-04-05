import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_lt_zpow_iff_right (ha : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_right_strictMono ha).lt_iff_lt


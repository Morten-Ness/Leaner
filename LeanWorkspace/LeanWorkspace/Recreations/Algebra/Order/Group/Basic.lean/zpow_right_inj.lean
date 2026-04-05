import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {m n : ℤ} {a b : α}

theorem zpow_right_inj (ha : 1 < a) {m n : ℤ} : a ^ m = a ^ n ↔ m = n := (zpow_right_strictMono ha).injective.eq_iff


import Mathlib

variable {α : Type*}

variable [DivisionRing α] {n : ℤ}

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]


import Mathlib

variable {F α β : Type*}

variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

theorem Even.neg_one_zpow (h : Even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]


import Mathlib

variable {F α β : Type*}

variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

theorem neg_one_zpow_eq_ite : (-1 : α) ^ n = if Even n then 1 else -1 := by
  obtain ⟨n, _⟩ := n.eq_nat_or_neg
  aesop (add safe (by rw [neg_one_pow_eq_ite]))


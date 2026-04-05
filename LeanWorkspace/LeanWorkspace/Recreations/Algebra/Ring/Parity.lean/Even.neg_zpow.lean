import Mathlib

variable {F α β : Type*}

variable [DivisionMonoid α] [HasDistribNeg α] {a : α} {n : ℤ}

theorem Even.neg_zpow : Even n → ∀ a : α, (-a) ^ n = a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [← Int.two_mul, zpow_mul, zpow_two, neg_mul_neg]


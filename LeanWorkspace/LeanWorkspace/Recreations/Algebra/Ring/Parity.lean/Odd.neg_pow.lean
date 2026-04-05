import Mathlib

variable {F α β : Type*}

variable [Monoid α] [HasDistribNeg α] {n : ℕ}

theorem Odd.neg_pow : Odd n → ∀ a : α, (-a) ^ n = -a ^ n := by
  rintro ⟨c, rfl⟩ a; simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg]


import Mathlib

variable {R : Type u}

variable [Monoid R] [HasDistribNeg R]

theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zero _)
  | n + 1 => (neg_one_pow_eq_or n).symm.imp
    (fun h ↦ by rw [pow_succ, h, neg_one_mul, neg_neg])
    (fun h ↦ by rw [pow_succ, h, one_mul])

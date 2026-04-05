import Mathlib

variable {F α β : Type*}

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

theorem neg_one_pow_eq_ite : (-1 : R) ^ n = if Even n then 1 else (-1) := by
  cases Nat.even_or_odd n with
  | inl h => rw [h.neg_one_pow, if_pos h]
  | inr h => rw [h.neg_one_pow, if_neg (by simpa using h)]


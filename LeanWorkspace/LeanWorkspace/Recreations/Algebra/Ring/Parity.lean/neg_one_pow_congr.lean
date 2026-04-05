import Mathlib

variable {F α β : Type*}

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

theorem neg_one_pow_congr (h : Even m ↔ Even n) : (-1 : R) ^ m = (-1) ^ n := by
  simp [h, neg_one_pow_eq_ite]


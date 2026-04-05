import Mathlib

variable {F α β : Type*}

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

theorem neg_one_pow_eq_neg_one_iff_odd (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = -1 ↔ Odd n := by simp [neg_one_pow_eq_ite, h.symm]


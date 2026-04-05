import Mathlib

variable {F α β : Type*}

variable {R : Type*} [Monoid R] [HasDistribNeg R] {m n : ℕ}

theorem neg_one_pow_eq_one_iff_even (h : (-1 : R) ≠ 1) :
    (-1 : R) ^ n = 1 ↔ Even n := by simp [neg_one_pow_eq_ite, h]


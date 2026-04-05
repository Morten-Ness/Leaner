import Mathlib

variable {R : Type u}

variable [Monoid R] [HasDistribNeg R]

theorem neg_pow' (a : R) (n : ℕ) : (-a) ^ n = a ^ n * (-1) ^ n := mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n


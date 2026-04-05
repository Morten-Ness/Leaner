import Mathlib

variable {R : Type u}

variable [Monoid R] [HasDistribNeg R]

theorem neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n := neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n


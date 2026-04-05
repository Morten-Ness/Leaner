import Mathlib

variable {R : Type u}

variable [CommRing R]

variable [NoZeroDivisors R] {a b : R}

theorem eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.1

-- Copies of the above CommRing lemmas for `Units R`.


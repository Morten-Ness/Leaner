import Mathlib

variable {R : Type u}

variable [CommRing R]

variable [NoZeroDivisors R] {a b : R}

theorem sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg


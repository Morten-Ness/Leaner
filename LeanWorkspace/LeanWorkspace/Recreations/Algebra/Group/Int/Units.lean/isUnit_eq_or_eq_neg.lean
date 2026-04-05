import Mathlib

variable {u v : ℤ}

theorem isUnit_eq_or_eq_neg (hu : IsUnit u) (hv : IsUnit v) : u = v ∨ u = -v := or_iff_not_imp_left.2 (Int.isUnit_ne_iff_eq_neg hu hv).1


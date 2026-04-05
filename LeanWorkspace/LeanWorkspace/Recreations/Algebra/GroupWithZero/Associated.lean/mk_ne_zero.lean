import Mathlib

variable {M : Type*}

variable [MonoidWithZero M]

theorem mk_ne_zero {a : M} : Associates.mk a ≠ 0 ↔ a ≠ 0 := not_congr Associates.mk_eq_zero


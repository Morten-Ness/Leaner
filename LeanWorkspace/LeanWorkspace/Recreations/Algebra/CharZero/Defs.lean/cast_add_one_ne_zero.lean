import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 := mod_cast n.succ_ne_zero


import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 := not_congr Nat.cast_eq_zero


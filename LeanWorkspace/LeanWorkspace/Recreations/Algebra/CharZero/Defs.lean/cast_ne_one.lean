import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 := Nat.cast_eq_one.not


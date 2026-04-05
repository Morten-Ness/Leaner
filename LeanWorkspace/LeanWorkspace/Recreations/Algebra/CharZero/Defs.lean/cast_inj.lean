import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n := Nat.cast_injective.eq_iff


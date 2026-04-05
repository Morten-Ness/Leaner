import Mathlib

variable {R : Type*}

variable [AddMonoidWithOne R] [CharZero R]

theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by rw [← cast_zero, Nat.cast_inj]


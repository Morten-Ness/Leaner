import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_mul_gcd_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H ⊢
  exact dvd_gcd_mul_of_dvd_mul H


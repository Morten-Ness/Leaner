import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_dvd_gcd_mul_right_right [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd m (n * k) := by
  grw [← dvd_mul_right]


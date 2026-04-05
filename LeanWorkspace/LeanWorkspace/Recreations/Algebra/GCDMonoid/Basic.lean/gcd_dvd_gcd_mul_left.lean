import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_dvd_gcd_mul_left [GCDMonoid α] (m n k : α) : gcd m n ∣ gcd (k * m) n := by
  grw [← dvd_mul_left]


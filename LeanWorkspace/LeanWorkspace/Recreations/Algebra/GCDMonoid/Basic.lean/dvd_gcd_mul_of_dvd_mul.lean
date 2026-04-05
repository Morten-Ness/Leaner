import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_gcd_mul_of_dvd_mul [GCDMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ gcd k m * n := (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).dvd


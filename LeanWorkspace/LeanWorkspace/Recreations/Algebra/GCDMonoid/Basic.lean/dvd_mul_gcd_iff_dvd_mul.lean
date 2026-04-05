import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_mul_gcd_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ m * gcd k n ↔ k ∣ m * n := ⟨fun h => h.trans (mul_dvd_mul dvd_rfl (gcd_dvd_right k n)), dvd_mul_gcd_of_dvd_mul⟩


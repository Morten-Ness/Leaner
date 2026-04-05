import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_gcd_mul_iff_dvd_mul [GCDMonoid α] {m n k : α} : k ∣ gcd k m * n ↔ k ∣ m * n := ⟨fun h => h.trans (mul_dvd_mul (gcd_dvd_right k m) dvd_rfl), dvd_gcd_mul_of_dvd_mul⟩


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_isUnit_iff_isRelPrime [GCDMonoid α] {a b : α} :
    IsUnit (gcd a b) ↔ IsRelPrime a b := ⟨fun h _ ha hb ↦ isUnit_of_dvd_unit (dvd_gcd ha hb) h, (· (gcd_dvd_left a b) (gcd_dvd_right a b))⟩


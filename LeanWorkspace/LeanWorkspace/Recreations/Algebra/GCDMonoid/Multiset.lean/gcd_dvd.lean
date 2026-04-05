import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a := Multiset.dvd_gcd.1 dvd_rfl _ h


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : gcd a b ∣ c)
    (hcab : c ∣ gcd a b) : gcd a b = normalize c := normalize_gcd a b ▸ normalize_eq_normalize habc hcab


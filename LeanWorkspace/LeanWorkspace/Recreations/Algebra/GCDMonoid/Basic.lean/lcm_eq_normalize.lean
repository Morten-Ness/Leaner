import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (habc : lcm a b ∣ c)
    (hcab : c ∣ lcm a b) : lcm a b = normalize c := normalize_lcm a b ▸ normalize_eq_normalize habc hcab


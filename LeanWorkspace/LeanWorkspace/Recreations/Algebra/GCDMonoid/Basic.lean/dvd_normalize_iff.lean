import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b := Units.dvd_mul_right


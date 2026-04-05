import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b := Units.mul_right_dvd


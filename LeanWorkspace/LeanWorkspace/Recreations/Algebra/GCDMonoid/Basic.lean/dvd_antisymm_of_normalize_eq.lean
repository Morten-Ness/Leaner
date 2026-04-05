import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem dvd_antisymm_of_normalize_eq [IsCancelMulZero α] {a b : α}
    (ha : normalize a = a) (hb : normalize b = b)
    (hab : a ∣ b) (hba : b ∣ a) : a = b := ha ▸ hb ▸ normalize_eq_normalize hab hba


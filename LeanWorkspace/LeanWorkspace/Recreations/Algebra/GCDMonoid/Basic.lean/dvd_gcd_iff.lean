import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c := Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ =>
    dvd_gcd hab hac


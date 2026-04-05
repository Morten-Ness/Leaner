import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd [GCDMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b := lcm_dvd_iff.2 ⟨hab, hcb⟩


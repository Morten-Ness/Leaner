import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

variable {p : α} (hp : Prime p)

theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b := ⟨Prime.dvd_or_dvd_of_dvd_lcm hp, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩


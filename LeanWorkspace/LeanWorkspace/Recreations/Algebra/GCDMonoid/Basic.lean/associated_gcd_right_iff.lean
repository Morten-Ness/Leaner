import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem associated_gcd_right_iff [GCDMonoid α] {x y : α} : Associated y (gcd x y) ↔ y ∣ x := ⟨fun hx => hx.dvd.trans (gcd_dvd_left x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd hxy dvd_rfl) (gcd_dvd_right x y)⟩


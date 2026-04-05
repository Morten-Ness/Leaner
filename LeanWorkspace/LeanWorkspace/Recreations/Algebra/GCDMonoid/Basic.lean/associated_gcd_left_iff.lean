import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem associated_gcd_left_iff [GCDMonoid α] {x y : α} : Associated x (gcd x y) ↔ x ∣ y := ⟨fun hx => hx.dvd.trans (gcd_dvd_right x y),
    fun hxy => associated_of_dvd_dvd (dvd_gcd dvd_rfl hxy) (gcd_dvd_left x y)⟩


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_greatest_associated {α : Type*} [CommMonoidWithZero α] [GCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    Associated d (GCDMonoid.gcd a b) := haveI h := hd _ (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  associated_of_dvd_dvd (GCDMonoid.dvd_gcd hda hdb) h


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_greatest {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α] {a b d : α}
    (hda : d ∣ a) (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) :
    GCDMonoid.gcd a b = normalize d := haveI h := hd _ (GCDMonoid.gcd_dvd_left a b) (GCDMonoid.gcd_dvd_right a b)
  gcd_eq_normalize h (GCDMonoid.dvd_gcd hda hdb)


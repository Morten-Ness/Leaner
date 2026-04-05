import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_dvd {b : β} (hb : b ∈ s) : s.gcd f ∣ f b := Finset.dvd_gcd_iff.1 dvd_rfl _ hb


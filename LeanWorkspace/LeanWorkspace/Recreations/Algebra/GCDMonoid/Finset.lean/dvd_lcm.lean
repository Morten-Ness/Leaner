import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem dvd_lcm {b : β} (hb : b ∈ s) : f b ∣ s.lcm f := Finset.lcm_dvd_iff.1 dvd_rfl _ hb


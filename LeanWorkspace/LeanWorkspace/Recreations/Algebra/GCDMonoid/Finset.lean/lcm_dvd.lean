import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_dvd {a : α} : (∀ b ∈ s, f b ∣ a) → s.lcm f ∣ a := Finset.lcm_dvd_iff.2


import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) := Multiset.lcm_singleton


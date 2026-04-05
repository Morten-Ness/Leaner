import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b) := Multiset.gcd_singleton


import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id := Eq.symm <| Finset.lcm_image _


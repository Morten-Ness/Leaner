import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id := Eq.symm <| Finset.gcd_image _


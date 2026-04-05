import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_cons {b : β} (h : b ∉ s) :
    (cons b s h : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := fold_cons h


import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [Finset.gcd_def]


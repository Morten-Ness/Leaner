import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem normalize_lcm : normalize (s.lcm f) = s.lcm f := by simp [Finset.lcm_def]


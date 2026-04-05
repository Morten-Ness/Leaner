import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_ne_zero_iff : s.gcd f ≠ 0 ↔ ∃ x ∈ s, f x ≠ 0 := by
  simp [Finset.gcd_eq_zero_iff]


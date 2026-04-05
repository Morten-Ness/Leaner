import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_ne_zero_iff [Nontrivial α] : s.lcm f ≠ 0 ↔ ∀ x ∈ s, f x ≠ 0 := by
  simp [Finset.lcm_eq_zero_iff]


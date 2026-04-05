import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]


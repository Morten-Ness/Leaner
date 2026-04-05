import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]


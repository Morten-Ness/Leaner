import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  exact Finset.fold_congr hfg


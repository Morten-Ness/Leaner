import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

theorem card_sigma {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) :
    #(s.sigma t) = ∑ a ∈ s, #(t a) := Multiset.card_sigma _ _


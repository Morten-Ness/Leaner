import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_sigma' {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a ∈ s, ∏ s ∈ t a, f a s) = ∏ x ∈ s.sigma t, f x.1 x.2 := Eq.symm <| Finset.prod_sigma s t fun x => f x.1 x.2


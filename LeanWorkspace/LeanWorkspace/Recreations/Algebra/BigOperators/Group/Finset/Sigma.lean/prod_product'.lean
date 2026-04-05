import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_product' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ x ∈ s, ∏ y ∈ t, f x y := Finset.prod_product ..


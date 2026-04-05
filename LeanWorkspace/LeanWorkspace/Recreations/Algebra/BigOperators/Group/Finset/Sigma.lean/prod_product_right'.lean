import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_product_right' (s : Finset γ) (t : Finset α) (f : γ → α → β) :
    ∏ x ∈ s ×ˢ t, f x.1 x.2 = ∏ y ∈ t, ∏ x ∈ s, f x y := Finset.prod_product_right ..


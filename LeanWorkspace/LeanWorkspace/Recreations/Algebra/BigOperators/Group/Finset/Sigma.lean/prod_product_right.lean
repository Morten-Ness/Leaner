import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_product_right (s : Finset γ) (t : Finset α) (f : γ × α → β) :
    ∏ x ∈ s ×ˢ t, f x = ∏ y ∈ t, ∏ x ∈ s, f (x, y) := Finset.prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm


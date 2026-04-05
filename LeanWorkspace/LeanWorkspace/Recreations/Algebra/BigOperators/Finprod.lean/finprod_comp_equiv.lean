import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_comp_equiv (e : α ≃ β) {f : β → M} : (∏ᶠ i, f (e i)) = ∏ᶠ i', f i' := finprod_comp e e.bijective


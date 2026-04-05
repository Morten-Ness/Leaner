import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_congr (h₀ : s = t) (h₁ : ∀ x ∈ t, f x = g x) :
    ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, g i := h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)


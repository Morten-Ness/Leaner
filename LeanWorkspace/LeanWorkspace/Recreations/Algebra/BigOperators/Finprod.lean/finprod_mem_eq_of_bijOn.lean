import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_eq_of_bijOn {s : Set α} {t : Set β} {f : α → M} {g : β → M} (e : α → β)
    (he₀ : s.BijOn e t) (he₁ : ∀ x ∈ s, f x = g (e x)) : ∏ᶠ i ∈ s, f i = ∏ᶠ j ∈ t, g j := by
  rw [← Set.BijOn.image_eq he₀, finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁


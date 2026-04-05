import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_prod_of_subset (f : α → M) {s : Set α} {t : Finset α}
    (h₁ : s ∩ mulSupport f ⊆ t) (h₂ : ↑t ⊆ s) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i := finprod_cond_eq_prod_of_cond_iff _ fun hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩


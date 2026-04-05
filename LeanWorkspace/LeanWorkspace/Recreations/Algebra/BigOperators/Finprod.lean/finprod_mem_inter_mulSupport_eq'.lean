import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_inter_mulSupport_eq' (f : α → M) (s t : Set α)
    (h : ∀ x ∈ mulSupport f, x ∈ s ↔ x ∈ t) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  apply finprod_mem_inter_mulSupport_eq
  ext x
  exact and_congr_left (h x)


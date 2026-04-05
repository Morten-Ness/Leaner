import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod_of_mulSupport_subset_of_finite (f : α → M) {s : Set α}
    (h : mulSupport f ⊆ s) (hs : s.Finite) : ∏ᶠ i, f i = ∏ i ∈ hs.toFinset, f i := finprod_eq_prod_of_mulSupport_subset f <| by rwa [Set.Finite.coe_toFinset]


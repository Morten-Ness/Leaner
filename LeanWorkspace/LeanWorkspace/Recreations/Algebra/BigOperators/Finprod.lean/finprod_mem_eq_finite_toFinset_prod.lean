import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_finite_toFinset_prod (f : α → M) {s : Set α} (hs : s.Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hs.toFinset, f i := finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by rw [hs.coe_toFinset]


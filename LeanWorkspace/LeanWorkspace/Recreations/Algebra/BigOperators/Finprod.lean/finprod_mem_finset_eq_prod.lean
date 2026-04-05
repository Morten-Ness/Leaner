import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_finset_eq_prod (f : α → M) (s : Finset α) : ∏ᶠ i ∈ s, f i = ∏ i ∈ s, f i := finprod_mem_eq_prod_of_inter_mulSupport_eq _ rfl


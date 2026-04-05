import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod_of_fintype [Fintype α] (f : α → M) : ∏ᶠ i : α, f i = ∏ i, f i := finprod_eq_prod_of_mulSupport_toFinset_subset _ (Set.toFinite _) <| Finset.subset_univ _


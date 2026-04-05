import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i := Set.multiset_prod_mem_multiset_prod _ _ _ hg


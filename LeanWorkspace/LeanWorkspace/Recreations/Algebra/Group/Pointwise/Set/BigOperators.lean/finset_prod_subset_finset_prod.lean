import Mathlib

variable {ι α β F : Type*} [FunLike F α β]

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : ∏ i ∈ t, f₁ i ⊆ ∏ i ∈ t, f₂ i := Set.multiset_prod_subset_multiset_prod _ _ _ hf


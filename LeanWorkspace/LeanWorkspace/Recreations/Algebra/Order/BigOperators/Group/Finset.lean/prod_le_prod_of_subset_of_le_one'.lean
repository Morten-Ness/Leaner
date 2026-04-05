import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_le_prod_of_subset_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} {s t : Finset ι} [MulLeftMono N] (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := Finset.prod_le_prod_of_subset_of_one_le' (N := Nᵒᵈ) h hf


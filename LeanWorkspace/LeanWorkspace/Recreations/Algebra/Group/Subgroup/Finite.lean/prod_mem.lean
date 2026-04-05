import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem prod_mem {G : Type*} [CommGroup G] (K : Subgroup G) {ι : Type*} {t : Finset ι}
    {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) : (∏ c ∈ t, f c) ∈ K := prod_mem h


import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (∀ a ∈ g, a ∈ K) → g.prod ∈ K := multiset_prod_mem g


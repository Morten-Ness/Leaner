import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K := K.toSubmonoid.multiset_noncommProd_mem g comm


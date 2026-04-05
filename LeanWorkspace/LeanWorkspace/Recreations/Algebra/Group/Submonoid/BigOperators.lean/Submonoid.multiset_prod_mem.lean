import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := multiset_prod_mem _root_ m hm


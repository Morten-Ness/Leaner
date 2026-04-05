import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)


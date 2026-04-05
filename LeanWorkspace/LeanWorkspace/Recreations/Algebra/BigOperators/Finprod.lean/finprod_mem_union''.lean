import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_union'' (hst : Disjoint (s ∩ mulSupport f) (t ∩ mulSupport f))
    (hs : (s ∩ mulSupport f).Finite) (ht : (t ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport f s, ← finprod_mem_inter_mulSupport f t, ←
    finprod_mem_union hst hs ht, ← union_inter_distrib_right, finprod_mem_inter_mulSupport]


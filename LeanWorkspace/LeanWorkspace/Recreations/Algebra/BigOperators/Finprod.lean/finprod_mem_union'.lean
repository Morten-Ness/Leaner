import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s ∩ mulSupport f).Finite)
    (ht : (t ∩ mulSupport f).Finite) : ∏ᶠ i ∈ s ∪ t, f i = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty,
    mul_one]


import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i := by
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
  · exact (finite_singleton a).inter_of_left _


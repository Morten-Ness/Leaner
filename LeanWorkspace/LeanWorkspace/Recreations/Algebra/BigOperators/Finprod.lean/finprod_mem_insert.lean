import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.Finite) :
    ∏ᶠ i ∈ insert a s, f i = f a * ∏ᶠ i ∈ s, f i := finprod_mem_insert' f h <| hs.inter_of_left _


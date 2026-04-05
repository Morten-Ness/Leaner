import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [LinearOrder M] {f g : ι → M} {s t : Finset ι}

theorem exists_lt_of_prod_lt' [MulLeftMono M] (Hlt : ∏ i ∈ s, f i < ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i < g i := by
  contrapose! Hlt with Hle
  exact Finset.prod_le_prod' Hle


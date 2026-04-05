import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [LinearOrder M] {f g : ι → M} {s t : Finset ι}

variable [IsOrderedCancelMonoid M]

theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact Finset.prod_lt_prod_of_nonempty' hs Hlt


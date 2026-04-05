import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem one_lt_prod [MulLeftStrictMono M] (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) :
    1 < ∏ i ∈ s, f i := lt_of_le_of_lt (by rw [prod_const_one]) <| Finset.prod_lt_prod_of_nonempty' hs h


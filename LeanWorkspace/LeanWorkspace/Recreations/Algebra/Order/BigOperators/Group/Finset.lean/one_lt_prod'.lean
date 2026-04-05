import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem one_lt_prod' [MulLeftStrictMono M] (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) :
    1 < ∏ i ∈ s, f i := prod_const_one.symm.trans_lt <| Finset.prod_lt_prod' h hs


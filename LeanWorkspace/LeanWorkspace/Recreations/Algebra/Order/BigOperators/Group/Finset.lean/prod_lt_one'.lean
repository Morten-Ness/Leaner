import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem prod_lt_one' [MulLeftStrictMono M] (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) :
    ∏ i ∈ s, f i < 1 := prod_const_one.le.trans_lt' <| Finset.prod_lt_prod' h hs


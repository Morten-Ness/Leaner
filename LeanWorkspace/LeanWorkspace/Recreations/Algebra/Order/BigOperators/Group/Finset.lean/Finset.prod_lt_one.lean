import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem prod_lt_one [MulLeftStrictMono M] (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) :
    ∏ i ∈ s, f i < 1 := (Finset.prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])


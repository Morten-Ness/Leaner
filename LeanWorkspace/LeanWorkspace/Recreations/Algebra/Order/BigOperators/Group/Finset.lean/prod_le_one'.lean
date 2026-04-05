import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_le_one' [MulLeftMono N] (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := (Finset.prod_le_prod' h).trans_eq (by rw [prod_const_one])


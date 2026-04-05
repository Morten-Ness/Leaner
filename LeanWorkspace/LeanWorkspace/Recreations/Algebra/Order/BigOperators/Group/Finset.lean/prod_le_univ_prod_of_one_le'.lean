import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_le_univ_prod_of_one_le' [MulLeftMono N] [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    ∏ x ∈ s, f x ≤ ∏ x, f x := Finset.prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ ↦ w a


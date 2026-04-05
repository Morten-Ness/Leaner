import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem single_le_prod' [MulLeftMono N] (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) :
    f a ≤ ∏ x ∈ s, f x := calc
    f a = ∏ i ∈ {a}, f i := (prod_singleton _ _).symm
    _ ≤ ∏ i ∈ s, f i :=
      Finset.prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ ↦ hf i hi


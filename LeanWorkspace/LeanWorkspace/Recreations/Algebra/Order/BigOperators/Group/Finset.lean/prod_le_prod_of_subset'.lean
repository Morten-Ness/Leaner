import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

theorem prod_le_prod_of_subset' (h : s ⊆ t) : ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  Finset.prod_le_prod_of_subset_of_one_le' h fun _ _ _ ↦ one_le _


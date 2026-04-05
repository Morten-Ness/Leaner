import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

theorem single_le_prod_of_canonicallyOrdered {i : ι} (hi : i ∈ s) :
    f i ≤ ∏ j ∈ s, f j := have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  Finset.single_le_prod' (fun _ _ ↦ one_le _) hi


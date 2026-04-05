import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

theorem prod_mono_set' (f : ι → M) : Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hs ↦
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  Finset.prod_le_prod_of_subset' hs


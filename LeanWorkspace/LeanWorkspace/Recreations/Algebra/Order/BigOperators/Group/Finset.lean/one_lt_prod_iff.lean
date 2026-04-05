import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

theorem one_lt_prod_iff {ι M : Type*} [CommMonoid M] [PartialOrder M] [CanonicallyOrderedMul M]
    {f : ι → M} {s : Finset ι} : 1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x := have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  Finset.one_lt_prod_iff_of_one_le <| fun _ _ => one_le _


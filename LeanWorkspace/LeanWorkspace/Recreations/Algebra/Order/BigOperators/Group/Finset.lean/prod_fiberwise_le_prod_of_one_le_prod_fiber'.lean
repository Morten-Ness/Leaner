import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

variable {ι' : Type*} [DecidableEq ι']

theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' [MulLeftMono N] {t : Finset ι'} {g : ι → ι'}
    {f : ι → N} (h : ∀ y ∉ t, (1 : N) ≤ ∏ x ∈ s with g x = y, f x) :
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤ ∏ x ∈ s, f x := calc
    (∏ y ∈ t, ∏ x ∈ s with g x = y, f x) ≤
        ∏ y ∈ t ∪ s.image g, ∏ x ∈ s with g x = y, f x :=
      Finset.prod_le_prod_of_subset_of_one_le' subset_union_left fun y _ ↦ h y
    _ = ∏ x ∈ s, f x :=
      prod_fiberwise_of_maps_to (fun _ hx ↦ mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _


import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_mono_set_of_one_le' [MulLeftMono N] (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hst ↦ Finset.prod_le_prod_of_subset_of_one_le' hst fun x _ _ ↦ hf x


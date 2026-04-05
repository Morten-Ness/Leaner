import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_anti_set_of_le_one'
    {ι : Type u_1} {N : Type u_5} [CommMonoid N] [Preorder N]
    {f : ι → N} [MulLeftMono N] (hf : ∀ (x : ι), f x ≤ 1) :
    Antitone fun (s : Finset ι) => ∏ x ∈ s, f x := fun _ _ hst ↦ Finset.prod_le_prod_of_subset_of_le_one' hst (by simp [hf])


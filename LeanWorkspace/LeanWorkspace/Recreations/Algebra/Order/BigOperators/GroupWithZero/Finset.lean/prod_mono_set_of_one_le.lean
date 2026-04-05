import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem prod_mono_set_of_one_le (hf : ∀ x, 1 ≤ f x) :
    Monotone fun s ↦ ∏ x ∈ s, f x := fun _ _ hst ↦ Finset.prod_le_prod_of_subset_of_one_le hst
    (fun i _ ↦ zero_le_one.trans (hf i)) (fun x _ _ ↦ hf x)


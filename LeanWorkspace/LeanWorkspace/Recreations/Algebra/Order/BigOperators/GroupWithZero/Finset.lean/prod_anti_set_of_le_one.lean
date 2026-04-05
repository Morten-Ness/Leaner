import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem prod_anti_set_of_le_one (hf0 : ∀ (x : ι), 0 ≤ f x) (hf : ∀ (x : ι), f x ≤ 1) :
    Antitone fun (s : Finset ι) => ∏ x ∈ s, f x := fun _ _ hst ↦ Finset.prod_le_prod_of_subset_of_le_one hst (by grind) (by simp [hf])


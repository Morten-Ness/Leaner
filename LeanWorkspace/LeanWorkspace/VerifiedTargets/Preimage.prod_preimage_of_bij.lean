import Mathlib

variable {ι κ β : Type*}

variable [CommMonoid β]

theorem prod_preimage_of_bij (f : ι → κ) (s : Finset κ) (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : κ → β) :
    ∏ x ∈ s.preimage f hf.injOn, g (f x) = ∏ x ∈ s, g x := Finset.prod_preimage _ _ hf.injOn g fun _ hs h_f ↦ (h_f <| hf.subset_range hs).elim


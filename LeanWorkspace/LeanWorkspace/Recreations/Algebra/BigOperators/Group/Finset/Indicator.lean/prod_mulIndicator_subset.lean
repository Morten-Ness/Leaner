import Mathlib

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_subset (f : ι → β) {s t : Finset ι} (h : s ⊆ t) :
    ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i := Finset.prod_mulIndicator_subset_of_eq_one _ (fun _ ↦ id) h fun _ ↦ rfl


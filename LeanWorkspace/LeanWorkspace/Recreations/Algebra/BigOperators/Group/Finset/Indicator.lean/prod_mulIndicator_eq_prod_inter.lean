import Mathlib

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι → β) :
    ∏ i ∈ s, (t : Set ι).mulIndicator f i = ∏ i ∈ s ∩ t, f i := by
  rw [← filter_mem_eq_inter, Finset.prod_mulIndicator_eq_prod_filter]; rfl


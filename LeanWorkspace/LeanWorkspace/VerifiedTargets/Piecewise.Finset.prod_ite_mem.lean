import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]


import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_dvd {f : α → N} (a : α) (hf : HasFiniteMulSupport f) : f a ∣ finprod f := by
  by_cases ha : a ∈ mulSupport f
  · rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((Finite.mem_toFinset hf).mpr ha)
  · rw [notMem_mulSupport.mp ha]
    exact one_dvd (finprod f)


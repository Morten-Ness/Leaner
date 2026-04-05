import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod_plift_of_mulSupport_toFinset_subset {f : α → M}
    (hf : HasFiniteMulSupport (f ∘ PLift.down)) {s : Finset (PLift α)} (hs : hf.toFinset ⊆ s) :
    ∏ᶠ i, f i = ∏ i ∈ s, f i.down := by
  rw [finprod, dif_pos hf]
  refine Finset.prod_subset hs fun x _ hxf => ?_
  rwa [hf.mem_toFinset, notMem_mulSupport] at hxf


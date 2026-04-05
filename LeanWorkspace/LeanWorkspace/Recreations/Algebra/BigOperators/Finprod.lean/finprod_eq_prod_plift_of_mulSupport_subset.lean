import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod_plift_of_mulSupport_subset {f : α → M} {s : Finset (PLift α)}
    (hs : mulSupport (f ∘ PLift.down) ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i.down := finprod_eq_prod_plift_of_mulSupport_toFinset_subset (s.finite_toSet.subset hs) fun x hx => by
    rw [Finite.mem_toFinset] at hx
    exact hs hx


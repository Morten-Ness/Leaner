import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_eq_prod_of_mulSupport_toFinset_subset (f : α → M) (hf : HasFiniteMulSupport f)
    {s : Finset α} (h : hf.toFinset ⊆ s) : ∏ᶠ i, f i = ∏ i ∈ s, f i := finprod_eq_prod_of_mulSupport_subset _ fun _ hx => h <| hf.mem_toFinset.2 hx


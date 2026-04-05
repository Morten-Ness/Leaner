import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_toFinset_prod (f : α → M) (s : Set α) [Fintype s] :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ s.toFinset, f i := finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp_rw [coe_toFinset s]


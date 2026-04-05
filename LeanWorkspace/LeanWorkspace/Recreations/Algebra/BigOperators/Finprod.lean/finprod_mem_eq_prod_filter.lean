import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_prod_filter (f : α → M) (s : Set α) [DecidablePred (· ∈ s)]
    (hf : HasFiniteMulSupport f) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset with i ∈ s, f i := finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by
    ext x
    simp [and_comm]


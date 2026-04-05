import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_prod (f : α → M) {s : Set α} (hf : (s ∩ mulSupport f).Finite) :
    ∏ᶠ i ∈ s, f i = ∏ i ∈ hf.toFinset, f i := finprod_mem_eq_prod_of_inter_mulSupport_eq _ <| by simp [inter_assoc]


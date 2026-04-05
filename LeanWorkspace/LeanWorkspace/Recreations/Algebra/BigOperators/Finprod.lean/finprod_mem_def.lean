import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_def (s : Set α) (f : α → M) : ∏ᶠ a ∈ s, f a = ∏ᶠ a, mulIndicator s f a := finprod_congr <| finprod_eq_mulIndicator_apply s f


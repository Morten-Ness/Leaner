import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_univ (f : α → M) : ∏ᶠ i ∈ @Set.univ α, f i = ∏ᶠ i : α, f i := finprod_congr fun _ => finprod_true _


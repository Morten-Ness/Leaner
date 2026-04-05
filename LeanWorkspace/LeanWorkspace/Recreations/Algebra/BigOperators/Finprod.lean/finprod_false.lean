import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_false (f : False → M) : ∏ᶠ i, f i = 1 := finprod_of_isEmpty _


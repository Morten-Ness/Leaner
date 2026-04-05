import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_of_not_hasFiniteMulSupport {f : α → M} (hf : ¬ f.HasFiniteMulSupport) :
    ∏ᶠ i, f i = 1 := finprod_of_infinite_mulSupport <| Set.not_finite.mp hf


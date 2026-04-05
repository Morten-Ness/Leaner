import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem map_finprod {G : Type*} [FunLike G M N] [MonoidHomClass G M N] (g : G)
    (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := (g : M →* N).map_finprod hf


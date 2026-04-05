import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem MonoidHom.map_finprod {f : α → M} (g : M →* N) (hf : HasFiniteMulSupport f) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := g.map_finprod_plift f <| hf.preimage Equiv.plift.injective.injOn


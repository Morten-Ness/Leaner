import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem MonoidHom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) := g.map_finprod_mem' (hs.inter_of_left _)


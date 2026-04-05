import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := f.map_finprod_plift g (Set.toFinite _)


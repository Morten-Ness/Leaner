import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MonoidHom.map_finprod_of_injective (g : M →* N) (hg : Function.Injective g) (f : α → M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := g.map_finprod_of_preimage_one (fun _ => (hg.eq_iff' g.map_one).mp) f


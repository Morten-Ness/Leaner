import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MulEquiv.map_finprod (g : M ≃* N) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := g.toMonoidHom.map_finprod_of_injective (EquivLike.injective g) f


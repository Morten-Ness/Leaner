import Mathlib

variable {ι κ M N β : Type*}

theorem MonoidHom.coe_finset_prod [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι) :
    ⇑(∏ x ∈ s, f x) = ∏ x ∈ s, ⇑(f x) := map_prod (MonoidHom.coeFn M N) _ _


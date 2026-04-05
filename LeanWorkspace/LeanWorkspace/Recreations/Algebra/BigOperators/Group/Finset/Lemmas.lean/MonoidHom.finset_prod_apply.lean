import Mathlib

variable {ι κ M N β : Type*}

theorem MonoidHom.finset_prod_apply [MulOneClass M] [CommMonoid N] (f : ι → M →* N) (s : Finset ι)
    (b : M) : (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b := map_prod (MonoidHom.eval b) _ _


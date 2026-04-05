import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem coe_finset_prod {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) := map_prod S.subtype f s


import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod := S.subtype.map_multiset_prod m


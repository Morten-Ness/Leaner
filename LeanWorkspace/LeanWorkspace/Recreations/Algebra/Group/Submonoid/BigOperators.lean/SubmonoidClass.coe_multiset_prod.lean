import Mathlib

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod := (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m


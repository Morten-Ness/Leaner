import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_coe (l : List M) : Multiset.prod ↑l = l.prod := rfl


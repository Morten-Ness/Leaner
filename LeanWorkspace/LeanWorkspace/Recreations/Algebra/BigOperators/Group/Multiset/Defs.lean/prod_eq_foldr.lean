import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_foldr (s : Multiset M) :
    Multiset.prod s = foldr (· * ·) 1 s := rfl


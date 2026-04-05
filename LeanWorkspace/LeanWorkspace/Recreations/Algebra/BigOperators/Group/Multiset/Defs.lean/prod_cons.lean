import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_cons (a : M) (s) : Multiset.prod (a ::ₘ s) = a * Multiset.prod s := foldr_cons _ _ _ _


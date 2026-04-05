import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_pair (a b : M) : ({a, b} : Multiset M).prod = a * b := by
  rw [insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]


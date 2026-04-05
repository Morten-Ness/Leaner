import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem pow_count [DecidableEq M] (a : M) : a ^ s.count a = (s.filter (Eq a)).prod := by
  rw [filter_eq, Multiset.prod_replicate]


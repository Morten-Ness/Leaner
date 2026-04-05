import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_one : Multiset.prod (m.map fun _ => (1 : M)) = 1 := by
  rw [map_const', Multiset.prod_replicate, one_pow]


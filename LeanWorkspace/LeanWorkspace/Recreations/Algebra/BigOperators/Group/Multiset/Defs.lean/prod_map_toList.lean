import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_map_toList (s : Multiset ι) (f : ι → M) : (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, coe_toList]


import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_toList (s : Multiset M) : s.toList.prod = s.prod := by
  conv_rhs => rw [← coe_toList s]
  rw [Multiset.prod_coe]


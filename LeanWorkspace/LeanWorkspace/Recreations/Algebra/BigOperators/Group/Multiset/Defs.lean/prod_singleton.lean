import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_singleton (a : M) : Multiset.prod {a} = a := by
  simp only [mul_one, Multiset.prod_cons, ← cons_zero, Multiset.prod_zero]


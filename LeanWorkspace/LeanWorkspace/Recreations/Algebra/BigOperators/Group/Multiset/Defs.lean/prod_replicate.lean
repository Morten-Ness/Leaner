import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  simp [replicate, List.prod_replicate]


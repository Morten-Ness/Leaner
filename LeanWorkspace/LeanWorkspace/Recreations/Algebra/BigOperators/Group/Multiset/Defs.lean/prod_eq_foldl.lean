import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_foldl (s : Multiset M) :
    Multiset.prod s = foldl (· * ·) 1 s := (foldr_swap _ _ _).trans (by simp [mul_comm])


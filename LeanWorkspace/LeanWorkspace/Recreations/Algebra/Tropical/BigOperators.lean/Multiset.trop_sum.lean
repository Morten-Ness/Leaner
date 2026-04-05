import Mathlib

variable {R S : Type*}

theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) := Quotient.inductionOn s (by simpa using List.trop_sum)


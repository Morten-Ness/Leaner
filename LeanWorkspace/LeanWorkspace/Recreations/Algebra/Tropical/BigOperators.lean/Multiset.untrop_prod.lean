import Mathlib

variable {R S : Type*}

theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) := Quotient.inductionOn s (by simpa using List.untrop_prod)


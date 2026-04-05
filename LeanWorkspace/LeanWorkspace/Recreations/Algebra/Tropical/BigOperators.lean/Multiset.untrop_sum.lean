import Mathlib

variable {R S : Type*}

theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]


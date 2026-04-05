import Mathlib

variable {R S : Type*}

theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]


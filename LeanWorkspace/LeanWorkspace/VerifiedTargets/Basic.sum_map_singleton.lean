import Mathlib

variable {F ι κ G M N O : Type*}

theorem sum_map_singleton (s : Multiset M) : (s.map fun a => ({a} : Multiset M)).sum = s := Multiset.induction_on s (by simp) (by simp)


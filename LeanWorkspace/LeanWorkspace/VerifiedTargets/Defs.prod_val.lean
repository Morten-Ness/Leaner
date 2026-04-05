import Mathlib

variable {ι κ M N G α : Type*}

theorem prod_val [CommMonoid M] (s : Finset M) : s.1.prod = s.prod id := by
  rw [Finset.prod, Multiset.map_id]


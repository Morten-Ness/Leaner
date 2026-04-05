import Mathlib

variable {ι M M₀ R : Type*}

variable [CommSemiring R]

theorem prod_map_sum {s : Multiset (Multiset R)} :
    prod (s.map sum) = sum ((Sections s).map prod) := Multiset.induction_on s (by simp) fun a s ih ↦ by
    simp [ih, map_bind, Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]


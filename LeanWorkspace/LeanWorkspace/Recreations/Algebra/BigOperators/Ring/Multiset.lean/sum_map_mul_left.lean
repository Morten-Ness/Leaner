import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] {a : R} {s : Multiset ι} {f : ι → R}

theorem sum_map_mul_left : sum (s.map fun i ↦ a * f i) = a * sum (s.map f) := Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]


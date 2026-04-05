import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] {a : R} {s : Multiset ι} {f : ι → R}

theorem sum_map_mul_right : sum (s.map fun i ↦ f i * a) = sum (s.map f) * a := Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]


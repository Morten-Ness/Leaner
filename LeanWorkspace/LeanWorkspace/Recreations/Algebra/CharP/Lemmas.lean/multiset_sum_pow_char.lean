import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R → R)).sum := map_multiset_sum (frobenius R p) _


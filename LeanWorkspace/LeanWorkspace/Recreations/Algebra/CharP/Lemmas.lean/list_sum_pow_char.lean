import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R → R)).sum := map_list_sum (frobenius R p) _


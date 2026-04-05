import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R → R)).sum := map_list_sum (iterateFrobenius R p n) _


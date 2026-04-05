import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem multiset_sum_pow_char_pow (s : Multiset R) :
    s.sum ^ p ^ n = (s.map (· ^ p ^ n : R → R)).sum := map_multiset_sum (iterateFrobenius R p n) _


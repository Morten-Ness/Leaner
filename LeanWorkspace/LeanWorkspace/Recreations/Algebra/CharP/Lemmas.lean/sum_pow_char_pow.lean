import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p ^ n = ∑ i ∈ s, f i ^ p ^ n := map_sum (iterateFrobenius R p n) _ _


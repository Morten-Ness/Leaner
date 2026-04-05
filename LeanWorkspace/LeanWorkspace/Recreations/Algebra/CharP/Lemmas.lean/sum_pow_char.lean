import Mathlib

variable {R S : Type*}

variable (R : Type*) [CommSemiring R]

variable (p n : ℕ) [ExpChar R p]

theorem sum_pow_char {ι : Type*} (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p := map_sum (frobenius R p) _ _


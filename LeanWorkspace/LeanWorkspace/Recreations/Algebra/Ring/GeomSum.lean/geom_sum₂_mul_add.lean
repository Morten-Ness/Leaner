import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

theorem geom_sum₂_mul_add (x y : R) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n := (Commute.all x y).geom_sum₂_mul_add n


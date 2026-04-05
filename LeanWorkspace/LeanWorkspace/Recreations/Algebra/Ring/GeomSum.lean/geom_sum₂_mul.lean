import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem geom_sum₂_mul (x y : R) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := (Commute.all x y).geom_sum₂_mul n


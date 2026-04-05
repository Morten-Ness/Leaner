import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

theorem geom_sum₂_comm (x y : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := (Commute.all x y).geom_sum₂_comm n


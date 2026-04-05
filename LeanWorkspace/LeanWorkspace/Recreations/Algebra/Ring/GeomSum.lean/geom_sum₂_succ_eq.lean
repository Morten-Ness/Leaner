import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem geom_sum₂_succ_eq (x y : R) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) = x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := (Commute.all x y).geom_sum₂_succ_eq


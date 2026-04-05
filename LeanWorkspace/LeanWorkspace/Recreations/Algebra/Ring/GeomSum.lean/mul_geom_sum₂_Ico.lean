import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem mul_geom_sum₂_Ico (x y : R) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := (Commute.all x y).mul_geom_sum₂_Ico hmn


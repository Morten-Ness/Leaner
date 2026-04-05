import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem geom_sum₂_with_one (x : R) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i := Finset.sum_congr rfl fun i _ => by rw [one_pow, mul_one]


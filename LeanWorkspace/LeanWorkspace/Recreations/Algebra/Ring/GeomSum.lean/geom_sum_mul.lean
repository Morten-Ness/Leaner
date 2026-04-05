import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem geom_sum_mul (x : R) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this


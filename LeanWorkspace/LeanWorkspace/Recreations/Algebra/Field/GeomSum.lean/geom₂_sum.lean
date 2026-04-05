import Mathlib

variable {R K : Type*}

variable [Field K] {x y : K}

theorem geom₂_sum (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) := (Commute.all x y).geom_sum₂ h n


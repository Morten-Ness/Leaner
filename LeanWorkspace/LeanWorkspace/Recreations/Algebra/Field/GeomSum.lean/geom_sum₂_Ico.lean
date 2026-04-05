import Mathlib

variable {R K : Type*}

variable [Field K] {x y : K}

theorem geom_sum₂_Ico (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) := (Commute.all x y).geom_sum₂_Ico hxy hmn


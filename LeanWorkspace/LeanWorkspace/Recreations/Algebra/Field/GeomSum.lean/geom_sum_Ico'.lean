import Mathlib

variable {R K : Type*}

variable [DivisionRing K] {x y : K}

theorem geom_sum_Ico' (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by
  simpa [geom_sum_Ico hx hmn] using neg_div_neg_eq (x ^ m - x ^ n) (1 - x)


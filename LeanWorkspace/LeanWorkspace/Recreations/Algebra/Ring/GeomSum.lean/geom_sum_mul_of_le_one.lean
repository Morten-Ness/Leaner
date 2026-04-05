import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

theorem geom_sum_mul_of_le_one (hx : x ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by simpa using geom_sum₂_mul_of_le hx n


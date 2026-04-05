import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

theorem geom_sum_mul_of_one_le (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by simpa using geom_sum₂_mul_of_ge hx n


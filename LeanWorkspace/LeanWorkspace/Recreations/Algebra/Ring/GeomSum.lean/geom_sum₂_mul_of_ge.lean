import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

theorem geom_sum₂_mul_of_ge (hxy : y ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

